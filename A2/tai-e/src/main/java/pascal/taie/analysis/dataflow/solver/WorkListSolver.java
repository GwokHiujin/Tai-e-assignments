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
import pascal.taie.ir.exp.Var;

import java.util.LinkedList;
import java.util.Queue;
import java.util.TreeSet;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // Add all basic blocks to worklist
        // Pick a basicBlock from Worklist
        // oldOut = out[B]
        // in[B] = \wedge(predecessor of B) out[]
        // out[B] = gen_B \wedge (in[B] - kill_B)
        // if (oldOut != out[B])
        // add all successors of B to worklist
        Queue<Node> worklist = new LinkedList<>();
        for (Node node : cfg) {
            if (!cfg.isEntry(node) && !cfg.isExit(node)) {
                worklist.add(node);
            }
        }

        while (!worklist.isEmpty()) {
            Node curBB = worklist.poll();
            Fact in = analysis.newInitialFact();
            Fact out = analysis.newInitialFact();
            Fact oldOut = result.getOutFact(curBB);

            for (Node predecessor : cfg.getPredsOf(curBB)) {
                analysis.meetInto(result.getOutFact(predecessor), in);
            }
            result.setInFact(curBB, in);

            analysis.transferNode(curBB, in, out);
            if (!eq(oldOut, out)) {
                worklist.addAll(cfg.getSuccsOf(curBB));
            }

            result.setOutFact(curBB, out);
        }
    }

    private boolean eq(Fact old, Fact cur) {
        if (old == null && cur != null) {
            return false;
        } else if (old != null && cur != null) {
            return old.equals(cur);
        }
        return true;
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
