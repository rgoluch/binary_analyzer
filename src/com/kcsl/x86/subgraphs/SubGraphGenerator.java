package com.kcsl.x86.subgraphs;

import static com.kcsl.x86.Importer.*;
import static com.kcsl.x86.support.SupportMethods.*;
import static com.kcsl.x86.short_circuit.ShortCircuitChecking.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Stack;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.notification.NotificationSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.kcsl.paths.counting.TopDownDFPathCounter;
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
		
		ArrayList<Node> nodesAdded = new ArrayList<Node>();
		
		for(Node n : subgraph.eval().nodes()) {
					
			if (n.taggedWith(XCSG.ControlFlowCondition) || n.taggedWith(XCSG.controlFlowExitPoint) || n.taggedWith("bin_loopback_tail")) {
				AtlasSet<Edge> outgoing = n.out(XCSG.ControlFlow_Edge);
				
				n.tag("bin_node");
				for(Edge e : outgoing) {
					
					Node goingTo = e.to();
					if (goingTo.taggedWith(XCSG.ControlFlowCondition) || goingTo.taggedWith(XCSG.Break) || goingTo.taggedWith(XCSG.controlFlowExitPoint) || goingTo.taggedWith("bin_loopback_tail")) {
						e.tag("bin_induced_edge");
						e.to().tag("bin_node");
						if (e.hasAttr(XCSG.conditionValue)) {
							String val = e.getAttr(XCSG.conditionValue).toString();
							e.putAttr(XCSG.name, val);
						}
					}
					else if (!nodesAdded.contains(e.to())){
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
							nodesAdded.add(n);
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
							nodesAdded.add(n);

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
								
								if (edgeIn.hasAttr(XCSG.conditionValue)) {
									String cVal = edgeIn.getAttr(XCSG.conditionValue).toString();
									inducedEdge.putAttr(XCSG.conditionValue, cVal);
									inducedEdge.putAttr(XCSG.name, cVal);
								}
							}
						}
						
						
					}
				}
				
			} 
		}
		
		ArrayList<Node> removeRoots = new ArrayList<Node>();
		for(Edge e : subgraph.eval().edges().tagged("remove_edge")) {
			if (e.from().taggedWith("bin_node") && e.to().taggedWith("remove_node") && !removeRoots.contains(e.from())) {
				removeRoots.add(e.from());
			}
		}
		
		ArrayList<EdgeToAdd> edgesToAdd = new ArrayList<EdgeToAdd>();
		for (Node n : removeRoots) {
			
			for (Edge e : n.out("remove_edge")) {
				
				Node nextNode = e.to();
				while (!nextNode.taggedWith(XCSG.ControlFlowCondition) && !nextNode.taggedWith(XCSG.controlFlowExitPoint) && !nextNode.taggedWith("bin_loopback_tail")) {
					
					AtlasSet<Edge> dagEdges = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge);
					if (dagEdges.size() != 0) {
						nextNode = dagEdges.one().to();
					}else if (nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge).size() > 0) {
						nextNode = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge).one().to();
					}
				}
				
				if (nextNode.taggedWith(XCSG.ControlFlowCondition) || nextNode.taggedWith(XCSG.controlFlowExitPoint) || nextNode.taggedWith("bin_loopback_tail")) {
					if (n.out("bin_induced_edge").size() < 2) {
						nextNode.tag("bin_node");
						
						String condVal = null;
						if (e.hasAttr(XCSG.conditionValue)) {
							condVal = e.getAttr(XCSG.conditionValue).toString();
						}
						
						EdgeToAdd temp = new EdgeToAdd(n,nextNode, condVal);
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
				if (e.conditionValue != null) {
					temp.putAttr(XCSG.conditionValue, e.conditionValue);
					temp.putAttr(XCSG.name, e.conditionValue);
				}
			}
		}
		
		return subgraph.nodes("bin_node").induce(Query.universe().edges("bin_induced_edge"));
	}
	
	private static class EdgeToAdd{
		private Node from; 
		private Node to;
		private String conditionValue;
		
		public EdgeToAdd(Node from, Node to, String s) {
			this.from = from; 
			this.to = to;
			this.conditionValue = s;
		}
	}
	
	public static Q singleSrcReturn(Q c, String name, int flag) {
		
//		Q f = my_function(name);
//		Q originalCFG = my_cfg(f);
		
		Q subgraph = scTransform(c, name);
		
//		if (subgraph == null) {
//			return null;
//		}
		
		Node functionNode = Graph.U.createNode();
		if (flag != 1) {
			functionNode.putAttr(XCSG.name, "single_src_return_"+name);
		}
		else {
			name = name.substring(17);
			functionNode.putAttr(XCSG.name, "isomorphic_checking_"+name);
		}
		functionNode.tag(XCSG.Function);
		functionNode.tag("consolidated_src");
		
		ArrayList<Node> leaves = new ArrayList<Node>();
		Map<Node, Node> recreatedNodes = new HashMap<Node, Node>();
		
		for (Edge e : subgraph.eval().edges()) {
			Iterable<String> i = e.from().tagsI();
			Node tempFromNode = Graph.U.createNode();
			tempFromNode.putAttr(XCSG.name, e.from().getAttr(XCSG.name).toString());
			
			for (String s : i) {
				tempFromNode.tag(s);
			}
			
			Iterable<String> iTo = e.to().tagsI();
			Node tempToNode = Graph.U.createNode();
			tempToNode.putAttr(XCSG.name, e.to().getAttr(XCSG.name).toString());
			
			for (String s : iTo) {
				tempToNode.tag(s);
			}
			
			Node checkFrom = recreatedNodes.get(e.from());
			Node checkTo = recreatedNodes.get(e.to());
			
			if (checkFrom == null && checkTo == null) {
				createSubGraphEdge(e, tempFromNode, tempToNode);
				subFunctionEdge(functionNode, tempFromNode);
				tempFromNode.tag("consolidated_src");
				
				subFunctionEdge(functionNode, tempToNode);
				tempToNode.tag("consolidated_src");
				
				recreatedNodes.put(e.from(), tempFromNode);
				recreatedNodes.put(e.to(), tempToNode);
			}
			else if (checkFrom == null && checkTo != null) {
				createSubGraphEdge(e, tempFromNode, checkTo);
				subFunctionEdge(functionNode, tempFromNode);
			
				tempFromNode.tag("consolidated_src");	
				recreatedNodes.put(e.from(), tempFromNode);
			}
			else if (checkFrom != null && checkTo == null) {
				createSubGraphEdge(e, checkFrom, tempToNode);
				subFunctionEdge(functionNode, tempToNode);
				
				
				tempToNode.tag("consolidated_src");
				recreatedNodes.put(e.to(), tempToNode);
			}
			else if (checkFrom != null && checkTo != null) {
				createSubGraphEdge(e, checkFrom, checkTo);
			}
			
			if (tempToNode.taggedWith(XCSG.controlFlowExitPoint)) {
				leaves.add(tempToNode);
			}
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


		for(Node n : leaves) {
			Edge temp = Graph.U.createEdge(n, exit);
			n.untag(XCSG.controlFlowExitPoint);
			temp.tag(XCSG.ControlFlow_Edge);
			temp.tag("isomorphic_edge");
		}

		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q singleSrc = x.contained().nodes("consolidated_src").induce(Query.universe().edges("isomorphic_edge"));
		//Need to make a new graph that contains the dummy return node and then return that
		
//		Q r = findSrcSubGraph(c);
		
		return singleSrc;
		
	}
	

	/**
	 * 
	 * @param name
	 * @return
	 */
	
	public static Q findSrcSubGraph(Q subgraph) {
		
//		Q subgraph = subGraphGenerator(name);

		for(Node n : subgraph.eval().nodes()) {
						
			if (n.taggedWith(XCSG.ControlFlowCondition)  || n.taggedWith(XCSG.controlFlowExitPoint) || n.taggedWith(XCSG.DoWhileLoop)) {
				AtlasSet<Edge> outgoing = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
				n.tag("src_node");
				
				for(Edge e : outgoing) {
					Node goingTo = e.to();
					if (goingTo.taggedWith(XCSG.ControlFlowCondition)  || goingTo.taggedWith(XCSG.controlFlowExitPoint) ) {
//						|| goingTo.out().tagged(XCSG.ControlFlowBackEdge).size() > 0
						e.tag("src_induced_edge");
						if (e.hasAttr(XCSG.conditionValue)) {
							String val = e.getAttr(XCSG.conditionValue).toString();
							e.putAttr(XCSG.name, val);
						}
						goingTo.tag("src_node");
					}
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
						
						if (successor.taggedWith(XCSG.ControlFlowCondition) && e.taggedWith(XCSG.ControlFlowBackEdge) && 
								in.size() == 1 && !predecessor.taggedWith(XCSG.ControlFlowCondition)) {
							n.tag("src_node");
							e.tag("src_induced_edge");
						}	
						 else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.ControlFlowCondition)) {
							addEdge = true;
							unTag = true;
						}
						else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.controlFlowExitPoint)) {
							addEdge = true;
							unTag = true;
						}
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
								String value = x.getAttr(XCSG.conditionValue).toString();
								inducedEdge.putAttr(XCSG.conditionValue, value);
								inducedEdge.putAttr(XCSG.name, value);
							}
							
							if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
								inducedEdge.tag(XCSG.ControlFlowBackEdge);
							}
						}
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
				while (!nextNode.taggedWith(XCSG.ControlFlowCondition) && !nextNode.taggedWith(XCSG.controlFlowExitPoint) 
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
						
						String condVal = null;
						if (e.hasAttr(XCSG.conditionValue)) {
							condVal = e.getAttr(XCSG.conditionValue).toString();
						}
						
						EdgeToAdd temp = new EdgeToAdd(n,nextNode, condVal);
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
				if (e.conditionValue != null) {
					temp.putAttr(XCSG.conditionValue, e.conditionValue);
					temp.putAttr(XCSG.name, e.conditionValue);
				}
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
		TopDownDFPathCounter t = new TopDownDFPathCounter();
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			Graph binSubGraph = findSubGraph(functionName).eval();
			
			
			if (functionName.contains("test") || binSubGraph.nodes().tagged("self_loop_node").size() > 0) {
				continue;
			}
			
			functionName = functionName.replace("sym_", "");			
			Q srcFunction = my_function(functionName);
			Q srcCFG = my_cfg(srcFunction);
			Graph subGraph = singleSrcReturn(srcCFG, functionName, 0).eval();
			
			
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
		TopDownDFPathCounter srcCounter = new TopDownDFPathCounter(true);
		
		long bin_total_gt_src = 0;
		long bin_total_lt_src = 0;
		long bin_total_eq_src = 0;
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			String srcFunctionName = functionName.replace("sym_", "");
			
			if(functionName.contains("test") || functionName.contains("lexan") || functionName.contains("xsh_tar")) {
				continue;
			}
						
			Q f = my_function(functionName);	
			Graph binCFG = my_cfg(f).eval();
			
			Q srcF = my_function(srcFunctionName);	
			Graph srcCFG = my_cfg(srcF).eval();
			
			Graph binSubGraph = findSubGraph(functionName).eval();
			Graph srcSubGraph = singleSrcReturn(srcF, srcFunctionName, 0).eval();
			
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
	
	public static void createSubGraphEdge(Edge e, Node f, Node t) {
		Edge cfgEdge = Graph.U.createEdge(f, t);
		cfgEdge.tag(XCSG.ControlFlow_Edge);
		Iterable<String> edgeTags = e.tagsI();
		for (String s : edgeTags) {
			cfgEdge.tag(s);
		}
		
		cfgEdge.tag("isomorphic_edge");

		if (e.hasAttr(XCSG.conditionValue)) {
			String conditionVal = e.getAttr(XCSG.conditionValue).toString();
			cfgEdge.putAttr(XCSG.conditionValue, conditionVal);
			if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
				cfgEdge.putAttr(XCSG.name, "true");
			}else if (e.getAttr(XCSG.conditionValue).toString().contains("false")){
				cfgEdge.putAttr(XCSG.name, "false");
			}else if (e.getAttr(XCSG.conditionValue).toString().contains("default")) {
				cfgEdge.putAttr(XCSG.name, "default");
			}
		}
		
		if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
			cfgEdge.tag(XCSG.ControlFlowBackEdge);
		}
		
	}
	
	public static void subFunctionEdge(Node functionNode, Node created) {
		Edge functionEdge = Graph.U.createEdge(functionNode, created);
		functionEdge.tag(XCSG.Contains);
	}
	
}
