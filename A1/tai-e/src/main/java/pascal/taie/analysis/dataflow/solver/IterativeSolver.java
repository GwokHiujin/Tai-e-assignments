/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Node node : cfg) {
                if (cfg.isExit(node)) {
                    continue;
                }
                // Node - current Basic Block B
                Fact inB = analysis.newInitialFact();
                Fact outB = analysis.newInitialFact();

                // OUT[B] = U_IN[successors_of_B]
                for (Node successor : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(successor), outB);
                }
                result.setOutFact(node, outB);

                // IN[B] = use_B U (OUT[B] - def_B)
                analysis.transferNode(node, inB, outB);

                if (!inB.equals(result.getInFact(node))) {
                    changed = true;
                    result.setInFact(node, inB);
                }
            }
        }
    }
}
