package extensions

import viper.silicon.rules.evaluator.eval
import viper.silicon.state.{Heap, State}
import viper.silicon.state.terms.{Sort, Term}
import viper.silicon.utils.{ast, freshSnap, toSf}
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.rules.producer
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast.utility.IterativeSimplifier
import viper.silver.ast.{Node, _}
import viper.silver.verifier.{AbstractError, Failure, PartialVerificationError}
import viper.silver.verifier.errors.IfFailed

import scala.collection.mutable
import scala.collection.mutable._

object SiliconIterativeSimplifier extends IterativeSimplifier {
  override def pfSimplify[N <: Node](n: N, assumeWelldefinedness: Boolean): ArrayBuffer[N] = super.pfSimplify(n, assumeWelldefinedness)


  def npfRecSimplify[N <: Node](n: N, s: State, v: Verifier, assumeWelldefinedness: Boolean): ArrayBuffer[N] = {
    val result: ArrayBuffer[N] = ArrayBuffer()
    result ++= pfSimplify(n, s, v, assumeWelldefinedness)
    val newChildrenList = n.children.zipWithIndex.map {
      case (child: AtomicType, index) => {
        ArrayBuffer()
      }
      case (child: N, index) => {
        val temp = new ArrayBuffer[List[Any]]()
        temp ++= pfSimplify(child, s, v, assumeWelldefinedness).map { pfSimpChild =>
          n.children.toList.updated(index, pfSimpChild)
        }
        temp ++= npfRecSimplify(child, s, v, assumeWelldefinedness).toList.map { recSimpChild =>
          n.children.toList.updated(index, recSimpChild)
        }
        temp
      }
      case _ => {
        ArrayBuffer()
      }
    }

    val newlist = newChildrenList.map {
      newChildren => newChildren.map{
        oneChildren => {
          n.withChildren(oneChildren) }//withChildren has big performance impact!
      }
    }
    newlist.map (listelem => result ++= listelem)
    result
  }

  def nsimplify[N <: Node](n: N, s: State, v: Verifier, assumeWelldefinedness: Boolean = false, iterationLimit: Integer = 5000, printToConsole: Boolean = false)(Q: Option[Exp] => VerificationResult): N = {

    val visited: ArrayBuffer[N] = ArrayBuffer(n)
    val queue: mutable.Queue[N] = mutable.Queue(n)

    while (queue.nonEmpty && visited.length < iterationLimit) {
      val currnode: N = queue.dequeue()
      if(printToConsole) {
        println("currnode: " + currnode)
      }

      val generated: ArrayBuffer[N] = pfRecSimplify(currnode, assumeWelldefinedness)
      //generated ++= nExtraCases(n, s, v, assumeWelldefinedness)(Q)

      if(printToConsole) {
        println("generated: " + generated)
      }
      for (g <- generated if !visited.contains(g)) {
        visited.append(g)
        queue.enqueue(g)
      }
    }

    if(printToConsole){
      println("result simplify: " + visited)
    }

    getShortest(visited)
  }

  /*def nExtraCases[N <: Node](n: N, s: State, v: Verifier, assumeWelldefinedness: Boolean)(Q: Option[Exp] => VerificationResult): ArrayBuffer[N] = {
    val listSimp: ArrayBuffer[N] = ArrayBuffer()

    listSimp ++= testStandalone(s, n, v)(Q)
  }*/


  def pfSimplify[N <: Node](n: N, s: State, v: Verifier, assumeWelldefinedness: Boolean): ArrayBuffer[N] = {

    val result: ArrayBuffer[N] = ArrayBuffer()
    result ++= pfSilverCases(n, assumeWelldefinedness)

    result
  }

  def checkRedAccField(s: State, exp: Exp, v: Verifier)(Q: Option[Exp] => VerificationResult): VerificationResult = {

    val simplifiedExp = exp
    val pve: PartialVerificationError = IfFailed(simplifiedExp)

    val imp = exp.topLevelConjuncts.collectFirst {case imp: Implies => imp}

    val rest = exp.topLevelConjuncts.filter(_ != imp)

    if(imp.isDefined) {
      for(oneImp <- imp) {

      }
    }

    imp match {
      case(Some(Implies(left, right))) => {
        val sExp: State = s.copy(h = Heap())
        //val sf: (Sort, Verifier) => Term = (sfS, sfV) => sfV
        producer.produces(
          sExp,
          freshSnap,
          rest,
          _ => pve,
          v
        ){ (s2, v2) =>
          eval(s2, left, pve, v2) { (s3, t, _, v3) =>
            val decis = v3.decider.check(t, 500)
            if(decis) {
              Q(Some(right))
            } else {
              Q(None)
            }
          }
        }
      }
    }

    val vExp: Exp = null
    Success()

  }

  def checkTestAcc(s: State, exp: Exp, v: Verifier)(Q: Option[Exp] => VerificationResult): VerificationResult = {
    val simplifiedExp = exp // .simplifySomehow(s, exp, v)
    val pve: PartialVerificationError = IfFailed(simplifiedExp)
    // Traverse exp for implies
    val imp = exp.topLevelConjuncts.collectFirst { case imp: Implies => imp }
    val rest = exp.topLevelConjuncts.filter(_ != imp)



    Some(exp) match {
      case Some(Implies(left, right)) =>
        val sExp: State = s.copy(h = Heap(), g = s.g)
        producer.produces(
          sExp,
          freshSnap,
          rest,
          _ => pve,
          v
        ){ (s2, v2) =>
          eval(s2, left, pve, v2) { (s3, t, _, v3) =>
            val decis = v3.decider.check(t, 500)
            if(decis) Q(Some(right)) else Q(None)
          }
        }
      case _ =>
        Q(None)
    }
  }

  def testStandalone(s: State, exp: Exp, v: Verifier)(Q: Option[Exp] => VerificationResult): ListBuffer[Exp] = {
    val listSimp = ListBuffer.empty[Exp]
    val Qtemp: Option[Exp] => VerificationResult = {
      res =>
        res match {
          case None => Success()
          case Some(simp) => {
            listSimp += simp
          }
        }
        Success()
    }

    val pve: PartialVerificationError = IfFailed(exp)
    // traverse exp for implies
    val impColl = exp.topLevelConjuncts.collect { case imp: Implies => imp }
    for(imp <- impColl) {
      val rest = exp.topLevelConjuncts.filter(_ != imp)

      Some(imp) match {
        case Some(Implies(left, right)) =>
          val sExp: State = s.copy(h = Heap(), g = s.g)
          producer.produces(
            sExp,
            freshSnap,
            rest,
            _ => pve,
            v
          ){ (s2, v2) =>
            eval(s2, left, pve, v2) { (s3, t, _, v3) =>
              val decis = v3.decider.check(t, 500)
              if(decis) Qtemp(Some(And(right, BigAnd(rest))())) else Q(None)
            }
          }
        case _ =>
          Qtemp(None)
      }
    }

    println(listSimp)
    listSimp
  }

  /*

  def verify(sInit: State, method: ast.Method): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, method.name, "-" * 10))

      val proverOptions: Map[String, String] = method.info.getUniqueInfo[ast.AnnotationInfo] match {
        case Some(ai) if ai.values.contains("proverArgs") =>
          toMap(ai.values("proverArgs").flatMap(o => {
            val index = o.indexOf("=")
            if (index == -1) {
              reporter report AnnotationWarning(s"Invalid proverArgs annotation ${o} on method ${method.name}. " +
                s"Required format for each option is optionName=value.")
              None
            } else {
              val (name, value) = (o.take(index), o.drop(index + 1))
              Some((name, value))
            }
          }))
        case _ =>
          Map.empty
      }
      v.decider.setProverOptions(proverOptions)

      openSymbExLogger(method)

      val pres = method.pres
      val posts = method.posts

      val body = method.bodyOrAssumeFalse.toCfg()
        /* TODO: Might be worth special-casing on methods with empty bodies */

      val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

      val ins = method.formalArgs.map(_.localVar)
      val outs = method.formalReturns.map(_.localVar)

      val g = Store(   ins.map(x => (x, decider.fresh(x)))
                    ++ outs.map(x => (x, decider.fresh(x)))
                    ++ method.scopedDecls.collect { case l: ast.LocalVarDecl => l }.map(_.localVar).map(x => (x, decider.fresh(x))))

      val s = sInit.copy(g = g,
                         h = Heap(),
                         oldHeaps = OldHeaps(),
                         methodCfg = body)

      checkTestAcc(s, pres.head, v){ res =>

        res match {
          case None => println("No simplification")
          //case Some(simp) => println("simplification")
          case Some(simp) => println(simp.toString)
        }
        Success()
      }

   */


}
