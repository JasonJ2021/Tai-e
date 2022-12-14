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

import java.util.HashSet;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        // result has been initialized
        Set<Node> worklist = new HashSet<>();
        for (Node basic_block : cfg) {
            worklist.add(basic_block);
        }
        while (!worklist.isEmpty()) {
            Node block = worklist.iterator().next();
            worklist.remove(block);
            for (Node pre : cfg.getPredsOf(block)) {
                analysis.meetInto(result.getOutFact(pre), result.getInFact(block));
            }
            if (analysis.transferNode(block, result.getInFact(block), result.getOutFact(block))) {
                for(Node successor : cfg.getSuccsOf(block))worklist.add(successor);
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Set<Node> worklist = new HashSet<>();
        for (Node basic_block : cfg) {
            worklist.add(basic_block);
        }
        while (!worklist.isEmpty()) {
            Node block = worklist.iterator().next();
            worklist.remove(block);
            for (Node success : cfg.getSuccsOf(block)) {
                analysis.meetInto(result.getInFact(success), result.getOutFact(block));
            }
            if (analysis.transferNode(block, result.getInFact(block), result.getOutFact(block))) {
                for(Node pred : cfg.getPredsOf(block))worklist.add(pred);
            }
        }

    }
}
