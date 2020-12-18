package com.kcsl.x86.subgraphs;

import static com.kcsl.x86.Importer.*;
import static com.kcsl.x86.support.SupportMethods.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.kcsl.paths.counting.TopDownDFMultiplicitiesPathCounter;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;

/**
 * 
 * @author RyanGoluch
 *
 */

public class SubGraphGenerator {
	
	/**
	 * 
	 */

	public static Q findSubGraph(String name) {

		Q f = my_function(name);	
		Q c = my_cfg(f);
		
		//Get all the nodes tagged with control flow conditions that would cause some form
		//of branching in the graph
		Q ifNodes = c.nodesTaggedWithAll(XCSG.ControlFlowIfCondition);		
		Q loopNodes = c.nodesTaggedWithAll(XCSG.ControlFlowLoopCondition);
		Q switchNodes = c.nodesTaggedWithAll(XCSG.ControlFlowSwitchCondition);
		Q exitNodes = c.nodesTaggedWithAll(XCSG.controlFlowExitPoint);
		
		//Find and generate the sub graph that is bounded above by if statements
		Q if_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, loopNodes);
		Q if_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, switchNodes);
		Q if_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, ifNodes);
		Q if_and_exits = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, exitNodes);
		
		Q if_subgraph = if_and_loops.union(if_and_switch).union(if_and_if).union(if_and_exits);
		
		//Find and generate the subgraph that is bounded above by loop conditions
		Q loops_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, ifNodes);
		Q loops_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, switchNodes);
		Q loops_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, loopNodes);
		Q loops_and_exits = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, exitNodes);
		
		Q loop_subgraph = loops_and_if.union(loops_and_switch).union(loops_and_loops).union(loops_and_exits);
		
		//Find and generate the subgraph that is bounded above by switch statements
		Q switch_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, ifNodes);
		Q switch_and_loop = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, ifNodes);
		Q switch_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, ifNodes);
		Q switch_and_exits = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, exitNodes);
		
		Q switch_subgraph = switch_and_if.union(switch_and_loop).union(switch_and_switch).union(switch_and_exits);		
		Q subgraph = if_subgraph.union(loop_subgraph).union(switch_subgraph);
		
		for(Node n : subgraph.eval().nodes()) {
					
			if (n.taggedWith(XCSG.ControlFlowCondition) || n.taggedWith(XCSG.controlFlowExitPoint) || n.taggedWith("bin_loopback_tail")) {
				AtlasSet<Edge> outgoing = n.out(XCSG.ControlFlow_Edge);
				
				n.tag("bin_node");
				for(Edge e : outgoing) {
					
					Node goingTo = e.to();
					AtlasSet<Edge> incoming = goingTo.in().taggedWithAny(XCSG.ControlFlow_Edge);
					AtlasSet<Edge> successorOut = goingTo.out().taggedWithAny(XCSG.ControlFlow_Edge);
//					if (!e.taggedWith("bin_induced_edge")) {
						if (goingTo.taggedWith(XCSG.ControlFlowCondition) || goingTo.taggedWith(XCSG.Break) || goingTo.taggedWith(XCSG.controlFlowExitPoint) || goingTo.taggedWith("bin_loopback_tail")) {
							e.tag("bin_induced_edge");
							e.to().tag("bin_node");
						}
//					}
					
					else {
						e.tag("remove_edge");
						e.to().tag("remove_node");
					}
				}
			}
//			else if (n.taggedWith("self_loop_node")) {
//				Node loopBody = Graph.U.createNode();
//				loopBody.tag(XCSG.ControlFlow_Node);
//				loopBody.tag("my_node");
//				loopBody.putAttr(XCSG.name, "loop body");
//				loopBody.tag("bin_node");
//				
//				Node function = n.oneIn(XCSG.Contains).from();
//				
//				Edge temp = Graph.U.createEdge(function, loopBody);
//				temp.tag(XCSG.Contains);
//				
//				Edge originalLoopBody = n.oneOut("self_loop_edge");
//				originalLoopBody.untag(XCSG.ControlFlowBackEdge);
//				
//				Edge headerToBody = Graph.U.createEdge(n, loopBody);
//				headerToBody.tag("bin_induced_edge");
//				
//				Edge bodyToHeader = Graph.U.createEdge(loopBody, n);
//				bodyToHeader.tag("bin_induced_edge");
//				bodyToHeader.tag(XCSG.ControlFlowBackEdge);
//				
//			}
			else {
				
				AtlasSet<Edge> in = n.in(XCSG.ControlFlow_Edge);
				AtlasSet<Edge> out = n.out().taggedWithAny(XCSG.ControlFlow_Edge);
				
				for (Edge edgeIn : in) {
					
					Node predecessor = edgeIn.from();
					Node successor = null;
					
					for (Edge e : out) {
						
						boolean addEdge = false;
						successor = e.to();
						if (successor.taggedWith(XCSG.ControlFlowCondition) && predecessor.taggedWith(XCSG.ControlFlowCondition)) {
							addEdge = true;
							if (edgeIn.taggedWith("remove_edge")) {
								edgeIn.untag("remove_edge");
							}
							if (n.taggedWith("remove_node")) {
								n.untag("remove_node");
							}
						}else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.controlFlowExitPoint)) {
							addEdge = true;
						}
						else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith("bin_loopback_tail")) {
							addEdge = true;
							if (edgeIn.taggedWith("remove_edge")) {
								edgeIn.untag("remove_edge");
							}
							if (n.taggedWith("remove_node")) {
								n.untag("remove_node");
							}
						}
						else {
							e.tag("remove_edge");
							successor.tag("remove_node");
							n.tag("remove_node");
						}
						
						if (addEdge) {
							if (predecessor.out().tagged("bin_induced_edge").size() < 2) {
								Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
								inducedEdge.tag("bin_induced_edge");
								successor.tag("bin_node");
							}
						}
						
						
					}
				}
				
			} 
		}
		
		Q removeNodes = subgraph.nodesTaggedWithAll("remove_node");
		Q removeSubGraph = subgraph.edgesTaggedWithAll("remove_edge").between(removeNodes, removeNodes);
		
		
		ArrayList<Node> removeRoots = new ArrayList<Node>();
		
		for(Edge e : subgraph.eval().edges().tagged("remove_edge")) {
			if (e.from().taggedWith("bin_node") && e.to().taggedWith("remove_node") && !removeRoots.contains(e.from())) {
				removeRoots.add(e.from());
			}
		}
		
//		System.out.println(removeRoots.size());
		ArrayList<EdgeToAdd> edgesToAdd = new ArrayList<EdgeToAdd>();
		
		for (Node n : removeRoots) {
			
			for (Edge e : n.out("remove_edge")) {
				
//				Edge edgeToCheck = n.out().tagged("remove_edge").one();
				Node nextNode = e.to();
				while (!nextNode.taggedWith(XCSG.ControlFlowCondition) && !nextNode.taggedWith(XCSG.controlFlowExitPoint)) {
					
					AtlasSet<Edge> dagEdges = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge);
//					nextNode = nextNode.out("REDIRECTED_CONTROL_FLOW_BACK_EDGE").one().to();
					if (dagEdges.size() != 0) {
						nextNode = dagEdges.one().to();
					}else if (nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge).size() > 0) {
						nextNode = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge).one().to();
					}
				}
				
				if (nextNode.taggedWith(XCSG.ControlFlowCondition) || nextNode.taggedWith(XCSG.controlFlowExitPoint)) {
					if (n.out("bin_induced_edge").size() < 2) {
						nextNode.tag("bin_node");
						EdgeToAdd temp = new EdgeToAdd(n,nextNode);
						if (!edgesToAdd.contains(temp)) {
							edgesToAdd.add(temp);

						}
					}
				}
			}
		}
		
		for (EdgeToAdd e : edgesToAdd) {
			if(e.from.out("bin_induced_edge").size() < 2) {
				Edge temp = Graph.U.createEdge(e.from, e.to);
				temp.tag("bin_induced_edge");
			}
		}
		
		return subgraph.nodes("bin_node").induce(Query.universe().edges("bin_induced_edge"));
	}
	
	private static class EdgeToAdd{
		private Node from; 
		private Node to; 
		
		public EdgeToAdd(Node from, Node to) {
			this.from = from; 
			this.to = to;
		}
		
		public Node getFrom() {
			return this.from;
		}
		
		public Node getTo() {
			return this.to;
		}
	}
	
	public static Q singleSrcReturn(String name) {
		
		Q f = my_function(name);
		Q subgraph = my_cfg(f);
		
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "dummy_"+name);
		functionNode.tag(XCSG.Function);
		functionNode.tag("consolidated_src");
		
		for (Node n : subgraph.eval().nodes()) {
			Edge tempEdge = Graph.U.createEdge(functionNode, n);
			tempEdge.tag(XCSG.Contains);
			n.tag("consolidated_src");
		}

		Node exit = Graph.U.createNode();
		exit.putAttr(XCSG.name, "src exit");
		exit.tag(XCSG.controlFlowExitPoint);
		exit.tag(XCSG.ControlFlow_Node);
		exit.tag("src_node");
		exit.tag("src_exit");
		exit.tag("consolidated_src");

		Edge tempExit = Graph.U.createEdge(functionNode, exit);
		tempExit.tag(XCSG.Contains);
		
		AtlasSet<Node> leaves = subgraph.eval().leaves();
//		System.out.println(leaves.size());

		for(Node n : leaves) {
			Edge temp = Graph.U.createEdge(n, exit);
//			temp.tag("src_induced_edge");
			n.untag(XCSG.controlFlowExitPoint);
			temp.tag(XCSG.ControlFlow_Edge);
		}

		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q c = x.contained().nodes("consolidated_src").induce(Query.universe().edges(XCSG.ControlFlow_Edge));
		//Need to make a new graph that contains the dummy return node and then return that
		
		Q r = findSrcSubGraph(c);
		
		return r;
		
	}
	

	/**
	 * 
	 * @param name
	 * @return
	 */
	
	public static Q findSrcSubGraph(Q subgraph) {
		
//		Q subgraph = subGraphGenerator(name);

		for(Node n : subgraph.eval().nodes()) {
			
//			if (n.out().tagged(XCSG.ControlFlowBackEdge).size() > 0) {
			
			if (n.taggedWith(XCSG.ControlFlowCondition)  || n.taggedWith("src_exit") || n.taggedWith(XCSG.DoWhileLoop)) {
//				|| n.taggedWith(XCSG.Break)
				AtlasSet<Edge> outgoing = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
				n.tag("src_node");
				
				for(Edge e : outgoing) {
					Node goingTo = e.to();
//					AtlasSet<Edge> incoming = goingTo.in().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
//					if (!e.taggedWith("src_induced_edge")) {
						if (goingTo.taggedWith(XCSG.ControlFlowCondition)  || goingTo.taggedWith("src_exit")
						|| goingTo.out().tagged(XCSG.ControlFlowBackEdge).size() > 0) {
//							|| goingTo.taggedWith(XCSG.Break)

							e.tag("src_induced_edge");
							goingTo.tag("src_node");
						}
//					}
//					else {
//						e.tag("remove_edge");
//						e.to().tag("remove_node");
//					}
				}
			} else {
				AtlasSet<Edge> in = n.in(XCSG.ControlFlow_Edge);
				AtlasSet<Edge> out = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
							
				for (Edge x : in) {
					
					Node predecessor = x.from();
					Node successor = null;
					
					for (Edge e : out) {
						
						boolean addEdge = false;
						boolean unTag = false;
						successor = e.to();
//						if (!e.taggedWith("src_induced_edge")) {
						if (successor.taggedWith(XCSG.ControlFlowCondition) && e.taggedWith(XCSG.ControlFlowBackEdge)) {
							n.tag("src_node");
							e.tag("src_induced_edge");
						}	
						 else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.ControlFlowCondition)) {
							addEdge = true;
							unTag = true;
						}
//						else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.Break)){
//							addEdge = true;
//							unTag = true;							
//						}
						else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith("src_exit")) {
							addEdge = true;
							unTag = true;
						}
//						else if (predecessor.taggedWith(XCSG.Break) && successor.taggedWith(XCSG.ControlFlowCondition)) {
//							addEdge = true;
//							unTag = true;
//						}else if (predecessor.taggedWith(XCSG.Break) && successor.taggedWith("src_exit")){
//							addEdge = true;
//							unTag = true; 
//						}
						else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.out(XCSG.ControlFlowBackEdge).size() > 0) {
							addEdge = true;
							unTag = true;
						}
						else {
							e.tag("remove_edge");
							x.tag("remove_edge");
							successor.tag("remove_node");
							n.tag("remove_node");
						}
						
						if (addEdge) {
							
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
							
							if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
								inducedEdge.tag(XCSG.ControlFlowBackEdge);
							}
							
							if(x.hasAttr(XCSG.conditionValue)) {
								inducedEdge.putAttr(XCSG.conditionValue, x.getAttr(XCSG.conditionValue).toString());
							}
							
							if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
								inducedEdge.tag(XCSG.ControlFlowBackEdge);
							}
						}
						
//						if (unTag) {
//							
//							if (x.taggedWith("remove_edge")) {
//								x.untag("remove_edge");
//							}
//							if (n.taggedWith("remove_node")) {
//								n.untag("remove_node");
//							}
//						}
						
					}
				}
				
				
				
			}
			
		}
		
		Q removeNodes = subgraph.nodesTaggedWithAll("remove_node");
		Q removeSubGraph = subgraph.edgesTaggedWithAll("remove_edge").between(removeNodes, removeNodes);
		AtlasSet<Node> roots = removeSubGraph.roots().eval().nodes();
		
		Map<Node, Edge> rootConditionEdges = new HashMap<Node, Edge>();
		for (Node n : roots) {
			AtlasSet<Edge> incomingConditionEdges = n.in();
			for(Edge e : incomingConditionEdges) {
				if(e.hasAttr(XCSG.conditionValue)) {
					rootConditionEdges.put(n, e);
				}
			}
		}
		
		ArrayList<Node> removeRoots = new ArrayList<Node>();
		ArrayList<EdgeToAdd> edgesToAdd = new ArrayList<EdgeToAdd>();
		
		for(Edge e : subgraph.eval().edges().tagged("remove_edge")) {
			if (e.from().taggedWith("src_node") && e.to().taggedWith("remove_node") && !removeRoots.contains(e.from())) {
				removeRoots.add(e.from());
			}
		}
		
		

		for (Node n : removeRoots) {
			
			for (Edge e : n.out("remove_edge")) {
				Node nextNode = e.to();
				while (!nextNode.taggedWith(XCSG.ControlFlowCondition) && !nextNode.taggedWith("src_exit") 
						&& !nextNode.taggedWith("src_node") && nextNode.taggedWith("remove_node")) {
					AtlasSet<Edge> dagEdges = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
					if (dagEdges.size() != 0) {
						nextNode = dagEdges.one().to();
					}
					else if (nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).size() > 0) {
						nextNode = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().to();
					}
				}
				
				if (nextNode.taggedWith("src_node")) {
					if (n.out("src_induced_edge").size() < n.out().size()) {
						nextNode.tag("src_node");
						EdgeToAdd temp = new EdgeToAdd(n,nextNode);
						if (!edgesToAdd.contains(temp)) {
							edgesToAdd.add(temp);
						}
					}
				}
			}
		}
		
		for (EdgeToAdd e : edgesToAdd) {
			if(e.from.out("src_induced_edge").size() < e.from.out().size()) {
				Edge temp = Graph.U.createEdge(e.from, e.to);
				temp.tag("src_induced_edge");
			}
		}
		
		return subgraph.nodes("src_node").induce(Query.universe().edges("src_induced_edge"));
//				subgraph.nodes("src_node").induce(Query.universe().edges("src_induced_edge"));
//				subgraph.nodes(XCSG.ControlFlow_Node).induce(Query.universe().edges(XCSG.ControlFlow_Edge));
	}
	
	
	public static void exportBinarySubGraphCounts() throws IOException {
		
		String subgraphCountsPath = "/Users/RyanGoluch/Desktop/binary_induced_graph_counts.csv";
		File countsFile = new File(subgraphCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		countsWriter.write("Function Name, # If Nodes, # Loop Nodes, # of Control Flow Nodes, Total Nodes in Subgraph, Induced Path Count, Original Path Count\n");
		countsWriter.flush();
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		MultiplicitiesPathCounter linearCounter = new MultiplicitiesPathCounter();

		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			Graph subGraph = findSubGraph(functionName).eval();
			Q f = my_function(functionName);	
			Graph binCFG = my_cfg(f).eval();
			
			if (functionName.contains("test") || subGraph.nodes().tagged("self_loop_node").size() > 0) {
				continue;
			}
			
//			System.out.println(functionName);
			
			long ifNodes = subGraph.nodes().tagged(XCSG.ControlFlowIfCondition).size();
			long loopNodes = subGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			long totalNodes = subGraph.nodes().size();
			long cfgNodes = totalNodes - (ifNodes + loopNodes);
			long induced = linearCounter.countPaths(Common.toQ(subGraph)).getPaths();
			long original = linearCounter.countPaths(Common.toQ(binCFG)).getPaths();
			
			countsWriter.write(functionName + ",");
			countsWriter.write(ifNodes + "," + loopNodes + "," + cfgNodes + "," + totalNodes + "," + induced + "," + original +"\n");
			countsWriter.flush();
		}
		
		countsWriter.close();
	}
	
	/**
	 * 
	 * @throws IOException
	 */
	
	public static void exportSourceSubGraphCounts() throws IOException {
		
		String subgraphCountsPath = "/Users/RyanGoluch/Desktop/source_induced_graph_counts.csv";
		File countsFile = new File(subgraphCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		countsWriter.write("Function Name, # If Nodes, # Loop Nodes, # Switch Nodes, # of Control Flow Nodes, Total Nodes in Subgraph, Induced Path Count, Original Path Count\n");
		countsWriter.flush();
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		TopDownDFMultiplicitiesPathCounter t = new TopDownDFMultiplicitiesPathCounter();
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			Graph binSubGraph = findSubGraph(functionName).eval();
			
			
			if (functionName.contains("test") || binSubGraph.nodes().tagged("self_loop_node").size() > 0) {
				continue;
			}
			
			functionName = functionName.replace("sym_", "");
//			System.out.println(functionName);
			
			Graph subGraph = singleSrcReturn(functionName).eval();
			Q srcFunction = my_function(functionName);
			Q srcCFG = my_cfg(srcFunction);
			
			long ifNodes = subGraph.nodes().tagged(XCSG.ControlFlowIfCondition).size();
			long loopNodes = subGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			long switchNodes = subGraph.nodes().tagged(XCSG.ControlFlowSwitchCondition).size();
			long totalNodes = subGraph.nodes().size();
			long cfgNodes = totalNodes - (ifNodes + loopNodes + switchNodes);
			long induced = t.countPaths(Common.toQ(subGraph)).getPaths().longValue();
			long original = t.countPaths(srcCFG).getPaths().longValue();
			
			countsWriter.write(functionName + ",");
			countsWriter.write(ifNodes + "," + loopNodes + "," + switchNodes + "," + cfgNodes + "," + totalNodes + "," + induced + "," + original + "\n");
			countsWriter.flush();
		}
		
		countsWriter.close();
	}
	
	/**
	 *
	 * @throws IOException 
	 */
	
	public static void exportAllSubGraphCounts() throws IOException {
		String subgraphCountsPath = "/Users/RyanGoluch/Desktop/Masters_Work/code_debugging/final_check/all_induced_graph_counts_updated.csv";
		File countsFile = new File(subgraphCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		String selfLoops = "/Users/RyanGoluch/Desktop/Masters_Work/code_debugging/final_check/all_induced_selfloop_graph_counts_updated.csv";
		File selfLoopFile = new File(selfLoops);
		BufferedWriter selfLoopsWriter = new BufferedWriter(new FileWriter(selfLoopFile)); 
		
		String lookInto = "/Users/RyanGoluch/Desktop/Masters_Work/code_debugging/final_check/binary_total_gt_src_functions.txt";
		File lookIntoFile = new File(lookInto);
		BufferedWriter lookIntoWriter = new BufferedWriter(new FileWriter(lookIntoFile));
		
		String difCount = "/Users/RyanGoluch/Desktop/Masters_Work/code_debugging/final_check/induced_path_dif_src_path.txt";
		File difFile = new File(difCount);
		BufferedWriter mismatch = new BufferedWriter(new FileWriter(difFile));
		
		String binOnly = "/Users/RyanGoluch/Desktop/Masters_Work/code_debugging/final_check/binary_only_functions.csv";
		File binOnlyFile = new File(binOnly);
		BufferedWriter binOnlyWriter = new BufferedWriter(new FileWriter(binOnlyFile));
		
		String oneNode = "/Users/RyanGoluch/Desktop/Masters_Work/code_debugging/final_check/one_node_or_path_functions.csv";
		File oneNodeFile = new File(oneNode);
		BufferedWriter oneNodeWriter = new BufferedWriter(new FileWriter(oneNodeFile));
		
		
		countsWriter.write("Function Name, # Induced Nodes (Bin), # Induced Nodes (Src), "
				+ "# Induced Edges (Bin), # Induced Edges (Src), # Loops (Bin), # Loops (Src), # Induced Paths (Bin), # Paths (Bin), # Induced Paths (Src), # Paths (Src)\n");
		countsWriter.flush();
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		MultiplicitiesPathCounter linearCounter = new MultiplicitiesPathCounter();
		TopDownDFMultiplicitiesPathCounter srcCounter = new TopDownDFMultiplicitiesPathCounter(true);
		
		long bin_total_gt_src = 0;
		long bin_total_lt_src = 0;
		long bin_total_eq_src = 0;
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			String srcFunctionName = functionName.replace("sym_", "");
			
			if(functionName.contains("test") || functionName.contains("lexan") || functionName.contains("xsh_tar")) {
				continue;
			}
			
//			System.out.println(functionName);
			
			Q f = my_function(functionName);	
			Graph binCFG = my_cfg(f).eval();
			
			Q srcF = my_function(srcFunctionName);	
			Graph srcCFG = my_cfg(srcF).eval();
			
			Graph binSubGraph = findSubGraph(functionName).eval();
			Graph srcSubGraph = singleSrcReturn(srcFunctionName).eval();
			
			
			
//			if (binSubGraph.nodes().size() > 0 && srcSubGraph.nodes().size() == 0) {
//				binOnlyWriter.write(functionName + "\n");
//				binOnlyWriter.flush();
//				continue;
//				
//			}
			
			if (binSubGraph.nodes().tagged("self_loop_node").size() > 0) {				
				selfLoopsWriter.write(functionName + "\n");
				selfLoopsWriter.flush();
				
				continue;
			}
			
			Long binInducedNodes = binSubGraph.nodes().tagged("bin_node").size();
			Long binInducedEdges = binSubGraph.edges().tagged("bin_induced_edge").size();
			Long binLoopNodes = binSubGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			
			Long binCFGPaths = linearCounter.countPaths(Common.toQ(binCFG)).getPaths();
			Long binInducedPaths = linearCounter.countPaths(Common.toQ(binSubGraph)).getPaths();
			
			Long srcInducedNodes = srcSubGraph.nodes().tagged("src_node").size();
			Long srcInducedEdges = srcSubGraph.edges().tagged("src_induced_edge").size();
			Long srcLoopNodes = srcSubGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			
			Long srcCFGPaths = srcCounter.countPaths(Common.toQ(srcCFG)).getPaths().longValue();
			Long srcInducedPaths = srcCounter.countPaths(Common.toQ(srcSubGraph)).getPaths().longValue();
			
			if(srcCFGPaths == 1 || binCFGPaths == 1) {
				oneNodeWriter.write(functionName + "\n");
				oneNodeWriter.flush();
				continue;
			}
			
			
			countsWriter.write(functionName + ",");
			countsWriter.write(binInducedNodes + "," + srcInducedNodes + ",");
			countsWriter.write(binInducedEdges + "," + srcInducedEdges + ",");
			countsWriter.write(binLoopNodes + "," + srcLoopNodes + ",");
			countsWriter.write(binInducedPaths + "," + binCFGPaths + ",");
			countsWriter.write(srcInducedPaths + "," + srcCFGPaths + "\n");
			countsWriter.flush();
			
			if(binCFGPaths != binInducedPaths) {
				mismatch.write(functionName + ", binary mismatch\n");
				mismatch.flush();
			}
			
			if(srcCFGPaths != srcInducedPaths) {
				mismatch.write(functionName + ", source mismatch\n");
				mismatch.flush();
			}
			
			if (binInducedPaths > srcInducedPaths) {
				bin_total_gt_src +=1;
				lookIntoWriter.write(functionName + "\n");
				lookIntoWriter.flush();
			}
			if (binInducedPaths < srcInducedPaths) {
				bin_total_lt_src +=1;
			}
			if (binInducedPaths == srcInducedPaths) {
				bin_total_eq_src +=1;
			}
		}
		
		countsWriter.write("\n");
		countsWriter.write("Path Counts:\n");
		countsWriter.write("Bin Total > Src Total, Bin Total < Src Total, Bin Total == Src Total\n");
		countsWriter.write(bin_total_gt_src + "," + bin_total_lt_src + "," + bin_total_eq_src);
		countsWriter.flush();

		oneNodeWriter.close();
		mismatch.close();
		countsWriter.close();
		lookIntoWriter.close();
	}
	
}
