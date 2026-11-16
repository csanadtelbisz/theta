/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import tools.refinery.store.map.Version
import tools.refinery.store.tuple.Tuple

/** A (partial) model state visited by Refinery, identified by its version in the model store. */
data class RefineryState(val version: Version, val depth: Int) : State {

  override fun isBottom(): Boolean = false
}

/** A fired Refinery transition rule with the node tuple it was activated on. */
data class RefineryAction(val ruleName: String, val activation: Tuple) : Action {

  override fun toString(): String = "$ruleName$activation"
}
