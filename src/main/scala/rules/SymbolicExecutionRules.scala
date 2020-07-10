// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.{Failure, SiliconNativeCounterexample, SiliconRawCounterexample, SiliconVariableCounterexample}
import viper.silicon.state.State
import viper.silicon.verifier.Verifier
import viper.silver.verifier.errors.ErrorWrapperWithExampleTransformer
import viper.silver.verifier.{Counterexample, CounterexampleTransformer, Model, VerificationError}

trait SymbolicExecutionRules extends Immutable {
  protected def createFailure(ve: VerificationError, v: Verifier, s: State, generateNewModel: Boolean = false): Failure = {
    var ceTrafo: Option[CounterexampleTransformer] = None
    val res = ve match {
      case ErrorWrapperWithExampleTransformer(wrapped, trafo) => {
        ceTrafo = Some(trafo)
        wrapped
      }
      case _ => ve
    }
    if (v != null && Verifier.config.counterexample.toOption.isDefined) {
      if (generateNewModel || v.decider.getModel() == null) {
        v.decider.generateModel()
      }
      val model = v.decider.getModel()
      if (!model.contains("model is not available")) {
        val nativeModel = Model(model)
        val ce: Counterexample = Verifier.config.counterexample.toOption.get match {
          case "native" =>
            val oldHeap = s.oldHeaps.get(Verifier.PRE_STATE_LABEL).map(_.values)
            SiliconNativeCounterexample(s.g, s.h.values, oldHeap, nativeModel)
          case "raw" =>
            val cs = (v.decider.pcs.assumptions ++ v.decider.pcs.branchConditions).toSeq
            SiliconRawCounterexample(cs, s, nativeModel)
          case _ => SiliconVariableCounterexample(s.g, nativeModel)
        }
        val finalCE = ceTrafo match {
          case Some(trafo) => trafo.f(ce)
          case _ => ce
        }
        res.counterexample = Some(finalCE)
      }
    }
    Failure(res)

  }
}