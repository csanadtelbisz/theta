/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm.rules;

import hu.bme.mit.theta.analysis.algorithm.mcm.EncodedRelationWrapper;
import hu.bme.mit.theta.analysis.algorithm.mcm.EventConstantLookup;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMRelation;
import hu.bme.mit.theta.common.TupleN;

import java.util.List;
import java.util.Objects;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class Toid extends UnaryMCMRule {
    public Toid(MCMRelation e) {
        super(e);
    }

    @Override
    public String toString() {
        return e.toString();
    }

    @Override
    public void encodeEvents(List<Integer> idList, EventConstantLookup resultEvents, EncodedRelationWrapper encodedRelationWrapper) {
        final EventConstantLookup events = e.encodeEvents(idList, encodedRelationWrapper);
        resultEvents.getAll().forEach((tuple, constDecl) -> {
            if (Objects.equals(tuple.get(0), tuple.get(1)))
                encodedRelationWrapper.getSolver().add(Iff(constDecl.getRef(), events.get(TupleN.of(tuple.get(0))).getRef()));
            else encodedRelationWrapper.getSolver().add(Not(constDecl.getRef()));
        });
    }
}