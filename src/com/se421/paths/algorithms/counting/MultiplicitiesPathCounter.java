package com.se421.paths.algorithms.counting;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;
import java.util.Collection;
//import java.util.

//import org.eclipse.core.internal.utils.Queue;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.graph.GraphElement.NodeDirection;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.log.Log;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.se421.paths.algorithms.PathCounter;
import com.se421.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.transforms.DAGTransform;

import com.se421.paths.results.*;


/**
 * This program counts all paths in a CFG by counting path multiplicities.
 * This implementation runs in O(n) time.
 * 
 * @author RyanGoluch
 */
public class MultiplicitiesPathCounter extends PathCounter{
	
	public MultiplicitiesPathCounter() {}

	/**
	 * Counts the number of paths in a given CFG
	 * 
	 * Example Atlas Shell Usage:
	 * var dskqopt = functions("dskqopt")
	 * var dskqoptCFG = cfg(dskqopt)
	 * var mCounter = new MultiplicitiesPathCounter
	 * mCounter.countPaths(dskqoptCFG)
	 * 
	 * @param cfg
	 * @return
	 */
	public CountingResult countPaths(Q cfg) {
		// the total number of paths discovered
		// and the number of additions required to count the path
		long numPaths = 0;
		long additions = 0;

		// create a directed acyclic graph (DAG)
		DAGTransform transformer = new DAGTransform();
		Q dag = transformer.transform(cfg);
		
		// the roots and leaves of the DAG
		AtlasSet<Node> dagLeaves = dag.leaves().eval().nodes();
		Node dagRoot = dag.roots().eval().nodes().one();
		
		// handle some trivial edge cases
		if(dagRoot == null) {
			// function is empty, there are no paths
			return new CountingResult(0L,0L);
		} else if(dagLeaves.contains(dagRoot)) {
			// function contains a single node there must be 1 path
			return new CountingResult(0L,1L);
		}
		
		//Log.info("num Leaves = " + dagLeaves.size());
		Stack<Node> stack = new Stack<Node>();
		stack.add(dagRoot);
		
		Map<Node, Long> mult = new HashMap<Node, Long>();
		Map<Node, Long> inEdge = new HashMap<Node, Long>();
		
		for (Node n : dag.eval().nodes()) {
			mult.put(n, 0L);
			AtlasSet<Edge> incomingControl = dag.reverseStep(Common.toQ(n)).eval().edges();
			inEdge.put(n, incomingControl.size());
		}
		mult.replace(dagRoot, 1L);
		
		long t = 0; 
		long m = 0;
		
		
		
		while(!stack.isEmpty()) {
			//stack.
			Node current = stack.pop();
		
			for(Node successor : dag.successors(Common.toQ(current)).eval().nodes()) {
			
				AtlasSet<Edge> incoming2 = successor.in();
				AtlasSet<Edge> incomingControl2 = Common.toQ(incoming2).edges(XCSG.ControlFlow_Edge).eval().edges();
				
				m = mult.get(successor)  + (mult.get(current) * dag.betweenStep(Common.toQ(current), Common.toQ(successor)).eval().edges().size());
				mult.put(successor, m);
				
				t = inEdge.get(successor) - dag.betweenStep(Common.toQ(current), Common.toQ(successor)).eval().edges().size();
				inEdge.put(successor, t);

				if (inEdge.get(successor) == 0) {
					stack.add(successor);
				}
			}
		}
		
		for(Node n : dagLeaves) {
			numPaths += mult.get(n);
			additions++;
		}
		
		// at the end, we have traversed all paths once, so return the count
		return new CountingResult(additions, numPaths);
	}
	
}
