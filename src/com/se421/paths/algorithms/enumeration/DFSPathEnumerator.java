package com.se421.paths.algorithms.enumeration;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.GraphElement.EdgeDirection;
import com.ensoftcorp.atlas.core.db.graph.GraphElement.NodeDirection;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.log.Log;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.se421.paths.algorithms.PathEnumerator;
import com.se421.paths.transforms.DAGTransform;
import com.se421.paths.results.*;

/**
 * This program counts all paths in the graph by iteratively enumerating all
 * paths. It uses a depth first traversal to walk the graph.
 * 
 * WARNING: This can be very expensive on large graphs! It's not only
 * potentially exp1Lntial in terms of the traversal, but also in terms of the
 * space to store each path!
 * 
 * @author RyanGoluch
 */
public class DFSPathEnumerator extends PathEnumerator {
	
	public DFSPathEnumerator() {}
	
	/**
	 * Counts the number of paths in a given CFG
	 * 
	 * Example Atlas Shell Usage:
	 * var dskqopt = functions("dskqopt")
	 * var dskqoptCFG = cfg(dskqopt)
	 * var enumerator = new DFSPathEnumerator
	 * enumerator.countPaths(dskqoptCFG)
	 */
	@Override
	public CountingResult countPaths(Q cfg) {
		return enumeratePaths(cfg).getCountingResult();
	}
	
	/**
	 * Enumerates each path in the given CFG and returns each
	 * path as a list of line numbers.
	 */
	@Override
	public EnumerationResult enumeratePaths(Q cfg) {
		// the total number of paths discovered
		List<List<Long>> paths = new ArrayList<List<Long>>();
		long additions = 0L;
		long np = 0L;
		
		// create a directed acyclic graph (DAG)
		DAGTransform transformer = new DAGTransform();
		Q dag = transformer.transform(cfg);
		
		// the roots and leaves of the DAG
		AtlasSet<Node> dagLeaves = dag.leaves().eval().nodes();
		Node dagRoot = dag.roots().eval().nodes().one();
		
		//Initialization
		Stack<Edge> stack = new Stack<Edge>();
		Map<Node, Long> depth = new HashMap<Node, Long>();
		//depth.put(dagRoot, 0L);
		for(Edge e : dag.forwardStep(Common.toQ(dagRoot)).eval().edges()) {
			stack.push(e);
			depth.put(e.to(), 0L);
		}
		
		List<Long> temp = new ArrayList<Long>();
		int count = 0; 
		temp.add(getLineNumber(dagRoot));
		
		while(!stack.isEmpty()) {
			Edge e = stack.pop();
			Node s = e.to();
			
			if (!depth.containsKey(s)) {
				if (!temp.contains(getLineNumber(s))) {
					temp.add(getLineNumber(s));
				}
				depth.put(s, depth.get(e.from()) + 1L);
			}
			
			if (dagLeaves.contains(s)) {
				np +=1;
				additions +=1;
				List<Long> temp2 = new ArrayList<Long>();
				temp2.addAll(temp);
				paths.add(temp2);
				temp.remove(getLineNumber(s));
				temp.remove(getLineNumber(e.from()));
				depth.remove(s);

			}
			else {
				for (Edge g : dag.forwardStep(Common.toQ(s)).eval().edges()) {
						stack.push(g);
				}
			}
		}
		
		// note that the size of paths is practically restricted to integer range, 
		// but this algorithm will exhaust memory long before it reaches the max range
		// since an enumeration result enumerates one path at a time, the number of 
		// additions will be the same as the number of paths in the counting result
		return new EnumerationResult(new CountingResult(paths.size(), paths.size()), paths);
	}
	
}
