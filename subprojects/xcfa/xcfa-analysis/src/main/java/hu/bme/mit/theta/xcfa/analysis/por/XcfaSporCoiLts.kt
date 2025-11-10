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
package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.xcfa.analysis.coi.transFuncVersion
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge

class XcfaSporCoiLts(xcfa: XCFA, coiLTS: LTS<S, A>) : XcfaSporLts(xcfa) {

  init {
    simpleXcfaLts = coiLTS
  }

  override fun <P : Prec> getEnabledActionsFor(
    state: S,
    exploredActions: Collection<A>,
    prec: P,
  ): Set<A> =
    getEnabledActions(state, simpleXcfaLts.getEnabledActionsFor(state, exploredActions, prec))

  override fun getEdge(action: A): XcfaEdge = super.getEdge(action.transFuncVersion ?: action)
}
