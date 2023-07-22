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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

public class EventConstantLookup {
    private final Map<TupleN<Integer>, ConstDecl<BoolType>> forward;
    private final Map<ConstDecl<BoolType>, TupleN<Integer>> reverse;

    public EventConstantLookup() {
        reverse = new LinkedHashMap<>();
        forward = new LinkedHashMap<>();
    }

    public void add(final TupleN<Integer> key, final ConstDecl<BoolType> value) {
        forward.put(key, value);
        reverse.put(value, key);
    }

    public TupleN<Integer> lookupKey(final ConstDecl<BoolType> value) {
        return reverse.get(value);
    }

    public ConstDecl<BoolType> get(final TupleN<Integer> key) {
        return forward.get(key);
    }

    public Collection<ConstDecl<BoolType>> getConstants() {
        return forward.values();
    }

    public Map<TupleN<Integer>, ConstDecl<BoolType>> getAll() {
        return forward;
    }
}