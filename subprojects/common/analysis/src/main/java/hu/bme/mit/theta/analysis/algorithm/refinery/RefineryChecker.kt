/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import tools.refinery.generator.standalone.StandaloneRefinery
import tools.refinery.language.semantics.ModelInitializer
import tools.refinery.store.dse.modification.ModificationAdapter
import tools.refinery.store.dse.propagation.PropagationAdapter
import tools.refinery.store.dse.transition.DesignSpaceExplorationAdapter
import tools.refinery.store.dse.transition.DesignSpaceExplorationStoreAdapter
import tools.refinery.store.model.ModelStore
import tools.refinery.store.query.ModelQueryAdapter
import tools.refinery.store.query.interpreter.QueryInterpreterAdapter
import tools.refinery.store.reasoning.ReasoningAdapter
import tools.refinery.store.reasoning.ReasoningStoreAdapter
import tools.refinery.store.statecoding.StateCoderAdapter
import tools.refinery.store.transition.system.TransitionSystemAdapter
import tools.refinery.store.transition.system.statespace.Trace as RefineryTrace
import tools.refinery.store.transition.system.strategy.TransitionSystemStoreManager
import tools.refinery.visualization.ModelVisualizerAdapter
import tools.refinery.visualization.internal.FileFormat

class RefineryChecker(
  private val problemString: String,
  private val logger: Logger,
) : SafetyChecker<Proof, Trace<out State, out Action>, UnitPrec> {

  override fun check(
    input: UnitPrec?
  ): SafetyResult<Proof, Trace<out State, out Action>> {
    val problem = StandaloneRefinery.getProblemLoader().loadString(problemString)
    val initializer = StandaloneRefinery.getInstance(ModelInitializer::class.java)
    initializer.readProblem(problem)

    val storeBuilder =
      ModelStore.builder()
        .with(QueryInterpreterAdapter.builder())
        .with(PropagationAdapter.builder())
        .with(StateCoderAdapter.builder())
        .with(ModificationAdapter.builder())
        .with(DesignSpaceExplorationAdapter.builder())
        .with(ReasoningAdapter.builder())
        .with(TransitionSystemAdapter.builder())
        .with(
          ModelVisualizerAdapter.builder()
            .withOutputPath("test_output")
            .withFormat(FileFormat.SVG)
            .saveStates()
            .saveDesignSpace()
        )

    initializer.configureStoreBuilder(storeBuilder)
    val store = storeBuilder.build()

    val solution =
      store
        .getAdapter(ReasoningStoreAdapter::class.java)
        .createInitialModel(initializer.modelSeed)
        .use { model ->
          val queryEngine = model.getAdapter(ModelQueryAdapter::class.java)
          val initialVersion = model.commit()
          queryEngine.flushChanges()

          val manager = TransitionSystemStoreManager(store)
          manager.startExploration(initialVersion)

          val visualizerAdapter = model.getAdapter(ModelVisualizerAdapter::class.java)
          val stateSpaceStore = store.getAdapter(DesignSpaceExplorationStoreAdapter::class.java).stateSpaceStore
          visualizerAdapter.visualize(stateSpaceStore, true)

          manager.solution
        }

    if (solution == null) {
      logger.writeln(Logger.Level.RESULT, "Refinery found no reachable target state.")
      return SafetyResult.safe(RefineryProof())
    }

    val trace = solution.toTrace()
    logger.writeln(Logger.Level.RESULT, "Refinery found a trace of length %d.", trace.length())
    logger.writeln(Logger.Level.DETAIL, "%s", trace.actions.joinToString("\n"))
    return SafetyResult.unsafe(trace, RefineryProof())
  }

  private fun RefineryTrace.toTrace(): Trace<RefineryState, RefineryAction> =
    Trace.of(
      states().map { RefineryState(it.version(), it.depth()) },
      transitions().map { RefineryAction(it.transition().toString(), it.activation()) },
    )
}
