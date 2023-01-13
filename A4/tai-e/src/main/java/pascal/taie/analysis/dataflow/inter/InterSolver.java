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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        workList = new SetQueue<>();
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        // 1.初始化ICFG中其他节点为initialfact
        for(Node node : icfg){
            result.setInFact(node,analysis.newInitialFact());
            result.setOutFact(node,analysis.newInitialFact());
        }
        // 2.需要初始化ICFG中的entry方法in(initialFact)/out fact(boundary)
        icfg.entryMethods().forEach((m)->{
            Node entry = icfg.getEntryOf(m);
            result.setInFact(entry,analysis.newInitialFact());
            result.setOutFact(entry,analysis.newBoundaryFact(entry));
        });

    }

    private void doSolve() {
        // TODO - finish me
        for (Node basic_block : icfg) {
            workList.add(basic_block);
        }
        while (!workList.isEmpty()) {
            Node block = workList.iterator().next();
            workList.remove(block);
            Fact in_block = result.getInFact(block);
            for (ICFGEdge<Node> pre_edge : icfg.getInEdgesOf(block)){
                Fact p_outFact = result.getOutFact(pre_edge.getSource()); // Get outfact of P
                analysis.meetInto(analysis.transferEdge(pre_edge , p_outFact),in_block);
            }
            if (analysis.transferNode(block, result.getInFact(block), result.getOutFact(block))) {
                workList.addAll(icfg.getSuccsOf(block));
            }
        }
    }
}
