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
package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.ArrayList;
import java.util.List;

public class COILogger {
    static long coiTimer = 0;
    static long transFuncTimer = 0;
    private static long startCoi = 0;
    private static long startTransFunc = 0;

    public static void startCoiTimer() {
        startCoi = System.currentTimeMillis();
    }

    public static void stopCoiTimer() {
        coiTimer += System.currentTimeMillis() - startCoi;
    }

    public static void startTransFuncTimer() {
        startTransFunc = System.currentTimeMillis();
    }

    public static void stopTransFuncTimer() {
        transFuncTimer += System.currentTimeMillis() - startTransFunc;
    }

    static long nops = 0;
    static List<Long> nopsList = new ArrayList<>();

    public static void incNops() {
        nops++;
    }

    public static void decNops() {
        nops--;
    }

    static long havocs = 0;
    static List<Long> havocsList = new ArrayList<>();

    public static void incHavocs() {
        havocs++;
    }

    public static void decHavocs() {
        havocs--;
    }

    static long allLabels = 0;
    static List<Long> allLabelsList = new ArrayList<>();

    public static void incAllLabels() {
        allLabels++;
    }

    static long exploredActions = 0;
    static List<Long> exploredActionsList = new ArrayList<>();

    public static void incExploredActions() {
        exploredActions++;
    }

    static long covers = 0;
    static List<Long> coversList = new ArrayList<>();

    public static void incCovers() {
        covers++;
    }

    public static void newIteration() {
        nopsList.add(nops);
        havocsList.add(havocs);
        allLabelsList.add(allLabels);
        exploredActionsList.add(exploredActions);
        coversList.add(covers);
        nops = 0;
        havocs = 0;
        allLabels = 0;
        exploredActions = 0;
        covers = 0;
    }

    static long staticAllLabels = 0;
    static long staticNops = 0;

    public static void incStaticAllLabels() {
        staticAllLabels++;
    }

    public static void incStaticNops() {
        staticNops++;
    }

    static long staticCoiTimer = 0;
    static long staticCoiDirectTimer = 0;
    static long staticCoiIndirectTimer = 0;
    static long startStaticCoi = 0;
    static long startStaticCoiDirect = 0;
    static long startStaticCoiIndirect = 0;

    public static void startStaticCoiTimer() {
        startStaticCoi = System.currentTimeMillis();
    }

    public static void stopStaticCoiTimer() {
        staticCoiTimer += System.currentTimeMillis() - startStaticCoi;
    }

    public static void startStaticCoiDirectTimer() {
        startStaticCoiDirect = System.currentTimeMillis();
    }

    public static void stopStaticCoiDirectTimer() {
        staticCoiDirectTimer += System.currentTimeMillis() - startStaticCoiDirect;
    }

    public static void startStaticCoiIndirectTimer() {
        startStaticCoiIndirect = System.currentTimeMillis();
    }

    public static void stopStaticCoiIndirectTimer() {
        staticCoiIndirectTimer += System.currentTimeMillis() - startStaticCoiIndirect;
    }
}
