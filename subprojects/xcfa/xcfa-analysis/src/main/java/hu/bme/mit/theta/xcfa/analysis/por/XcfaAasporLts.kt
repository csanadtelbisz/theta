/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.XCFA

class XcfaAasporLts(
    xcfa: XCFA,
    private val ignoredVariableRegistry: MutableMap<Decl<out Type>, MutableSet<ExprState>>
) : XcfaSporLts(xcfa) {

    override fun <P : Prec> getEnabledActionsFor(
        state: XcfaState<*>,
        exploredActions: Collection<XcfaAction>,
        prec: P
    ): Set<XcfaAction> {
        // Collecting enabled actions
        val allEnabledActions = getAllEnabledActionsFor(state)

        // Calculating the persistent set starting from every (or some of the) enabled transition or from exploredActions if it is not empty
        // The minimal persistent set is stored
        var minimalPersistentSet = mutableSetOf<XcfaAction>()
        val persistentSetFirstActions = if (exploredActions.isEmpty()) {
            getPersistentSetFirstActions(allEnabledActions)
        } else {
            setOf(exploredActions)
        }
        var finalIgnoredVariables = setOf<Decl<out Type>>()

        // Calculate persistent sets from all possible starting action set
        for (firstActions in persistentSetFirstActions) {
            // Variables that have been ignored (if they would be in the precision, more actions have had to be added to the persistent set)
            val ignoredVariables = mutableSetOf<Decl<out Type>>()
            val persistentSet = calculatePersistentSet(allEnabledActions, firstActions, prec, ignoredVariables)
            if (minimalPersistentSet.isEmpty() || persistentSet.size < minimalPersistentSet.size) {
                minimalPersistentSet = persistentSet.toMutableSet()
                finalIgnoredVariables = ignoredVariables
            }
        }
        finalIgnoredVariables.forEach { ignoredVariable ->
            if (!ignoredVariableRegistry.containsKey(ignoredVariable)) {
                ignoredVariableRegistry[ignoredVariable] = mutableSetOf()
            }
            ignoredVariableRegistry[ignoredVariable]!!.add(state)
        }
        minimalPersistentSet.removeAll(exploredActions.toSet())
        return minimalPersistentSet
    }

    /**
     * Calculates a persistent set of enabled actions starting from a set of particular actions.
     *
     * @param enabledActions the enabled actions in the present state
     * @param firstActions the actions that will be added to the persistent set as the first actions
     * @param prec the precision of the current abstraction
     * @param ignoredVariables variables that have been ignored (if they would be in the precision, more actions have had to be added to the persistent set)
     * @return a persistent set of enabled actions in the current abstraction
     */
    private fun calculatePersistentSet(enabledActions: Collection<XcfaAction>, firstActions: Collection<XcfaAction>, prec: Prec, ignoredVariables: MutableSet<Decl<out Type>>): Set<XcfaAction> {
        if (firstActions.any(this::isBackwardAction)) {
            return enabledActions.toSet()
        }

        val persistentSet = firstActions.toMutableSet()
        val otherActions = enabledActions.toMutableSet() // actions not in the persistent set
        firstActions.forEach(otherActions::remove)
        val ignoredVariablesByAction = otherActions.associateWith { mutableSetOf<Decl<out Type>>() }

        var addedNewAction = true
        while (addedNewAction) {
            addedNewAction = false
            val actionsToRemove = mutableSetOf<XcfaAction>()
            for (action in otherActions) {
                // for every action that is not in the persistent set it is checked whether it should be added to the persistent set
                // (because it is dependent with an action already in the persistent set)
                val potentialIgnoredVariables = mutableSetOf<Decl<out Type>>()
                if (persistentSet.any { persistentSetAction ->
                        areDependents(persistentSetAction, action, prec, potentialIgnoredVariables)
                    }) {
                    if (isBackwardAction(action)) {
                        return enabledActions.toSet() // see POR algorithm for the reason of removing backward transitions
                    }
                    persistentSet.add(action)
                    actionsToRemove.add(action)
                    addedNewAction = true
                } else {
                    ignoredVariablesByAction[action]!!.addAll(potentialIgnoredVariables) // the action is not added to the persistent set because we ignore variables in potentialIgnoredVariables
                }
            }
            actionsToRemove.forEach(otherActions::remove)
        }
        otherActions.forEach { action -> ignoredVariables.addAll(ignoredVariablesByAction[action]!!) }
        return persistentSet
    }

    private fun isIgnorable(varDecl: Decl<out Type>, prec: Prec) = varDecl !in prec.usedVars

    private fun areDependents(persistentSetAction: XcfaAction, action: XcfaAction, prec: Prec, ignoredVariables: MutableSet<Decl<out Type>>): Boolean {
        if (isSameProcess(persistentSetAction, action)) {
            return true
        }

        val usedByPersistentSetAction = getCachedUsedSharedObjects(getTransitionOf(persistentSetAction))
        val influencedSharedObjects = getInfluencedSharedObjects(getTransitionOf(action))
        for (varDecl in influencedSharedObjects) {
            if (usedByPersistentSetAction.contains(varDecl)) {
                if (isIgnorable(varDecl, prec)) {
                    // the actions would be dependent, but we may have a chance to ignore it in the current abstraction
                    ignoredVariables.add(varDecl)
                    continue
                }
                return true
            }
        }
        return false
    }
}