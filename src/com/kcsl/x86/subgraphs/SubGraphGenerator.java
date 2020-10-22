package com.kcsl.x86.subgraphs;

import static com.kcsl.x86.Importer.*;
import static com.kcsl.x86.support.SupportMethods.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
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

//		Q c = subGraphGenerator(name);
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
//		System.out.println(subgraph.eval().nodes().size());
		for(Node n : subgraph.eval().nodes()) {
					
			if (n.taggedWith(XCSG.ControlFlowCondition) || n.taggedWith(XCSG.controlFlowExitPoint) 
					|| n.in(XCSG.ControlFlow_Edge).size() >=2 || n.taggedWith("bin_loopback_tail")) {
				AtlasSet<Edge> outgoing = n.out(XCSG.ControlFlow_Edge);
				
				n.tag("bin_node");
				for(Edge e : outgoing) {
					
					Node goingTo = e.to();
					AtlasSet<Edge> incoming = goingTo.in().taggedWithAny(XCSG.ControlFlow_Edge);
					if (!e.taggedWith("bin_induced_edge")) {
						if (goingTo.taggedWith(XCSG.ControlFlowCondition) || goingTo.taggedWith(XCSG.Break) || goingTo.taggedWith(XCSG.controlFlowExitPoint) 
								|| incoming.size() >=2 || goingTo.taggedWith("bin_loopback_tail")) {
							e.tag("bin_induced_edge");
							e.to().tag("bin_node");
						}
					}
					
					else {
						e.tag("remove_edge");
						e.to().tag("remove_node");
					}
				}
			}else {
				
				Edge in = n.in(XCSG.ControlFlow_Edge).one();
				AtlasSet<Edge> out = n.out().taggedWithAny(XCSG.ControlFlow_Edge);
				Node predecessor = in.from();
				Node successor = null;
				
				for (Edge e : out) {
					boolean addEdge = false;
					successor = e.to();
					if (successor.taggedWith(XCSG.ControlFlowCondition) && predecessor.taggedWith(XCSG.ControlFlowCondition)) {
						addEdge = true;
					}else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.controlFlowExitPoint)) {
						addEdge = true;
						if (n.taggedWith("remove_node")) {
							n.untag("remove_node");
							in.untag("remove_edge");
						}
					}
					else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.in(XCSG.ControlFlow_Edge).size() >=2) {
						addEdge = true;
					}
					else if (predecessor.in(XCSG.ControlFlow_Edge).size() >=2 && successor.taggedWith(XCSG.controlFlowExitPoint)) {
						addEdge = true;
					}
					else if (predecessor.in(XCSG.ControlFlow_Edge).size() >=2 && successor.taggedWith(XCSG.ControlFlowCondition)) {
						addEdge = true;
					}
					else if (predecessor.in(XCSG.ControlFlow_Edge).size() >=2 && successor.in(XCSG.ControlFlow_Edge).size() >=2) {
						addEdge = true;
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
		
		Q removeNodes = subgraph.nodesTaggedWithAll("remove_node");
		Q removeSubGraph = subgraph.edgesTaggedWithAll("remove_edge").between(removeNodes, removeNodes);

		for (Node n : removeSubGraph.roots().eval().nodes()) {
			
			Node nextNode = n.out().tagged(XCSG.ControlFlow_Edge).one().to();
			while (!nextNode.taggedWith(XCSG.ControlFlowCondition) && !nextNode.taggedWith(XCSG.controlFlowExitPoint)) {
				
				AtlasSet<Edge> dagEdges = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge);
//				nextNode = nextNode.out("REDIRECTED_CONTROL_FLOW_BACK_EDGE").one().to();
				if (dagEdges.size() != 0) {
					nextNode = dagEdges.one().to();
				}else if (nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge).size() > 0) {
					nextNode = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge).one().to();
				}
			}
			if (nextNode.taggedWith(XCSG.ControlFlowCondition) || nextNode.taggedWith(XCSG.controlFlowExitPoint)) {
				Edge inducedEdge = Graph.U.createEdge(n.in(XCSG.ControlFlow_Edge).one().from(), nextNode);
				inducedEdge.tag("bin_induced_edge");
				nextNode.tag("bin_node");
			}
		}
//		return removeSubGraph;
		return subgraph.nodes("bin_node").induce(Query.universe().edges("bin_induced_edge"));
	}
	

	/**
	 * 
	 * @param name
	 * @return
	 */
	
	public static Q findSrcSubGraph(String name) {
		Q subgraph = subGraphGenerator(name);

		for(Node n : subgraph.eval().nodes()) {
			
//			if (n.out().tagged(XCSG.ControlFlowBackEdge).size() > 0) {
			
			if (n.taggedWith(XCSG.ControlFlowCondition) || n.taggedWith(XCSG.Break) 
					|| n.in().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).size() >=2 || n.taggedWith(XCSG.controlFlowExitPoint)) {
				AtlasSet<Edge> outgoing = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);

				n.tag("src_node");
				for(Edge e : outgoing) {
					Node goingTo = e.to();
					AtlasSet<Edge> incoming = goingTo.in().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
					if (!e.taggedWith("src_induced_edge")) {
						if (goingTo.taggedWith(XCSG.ControlFlowCondition) || goingTo.taggedWith(XCSG.Break) || goingTo.taggedWith(XCSG.controlFlowExitPoint)
								|| incoming.size() >=2 || goingTo.out().tagged(XCSG.ControlFlowBackEdge).size() > 0) {
							e.tag("src_induced_edge");
							e.to().tag("src_node");
							
//							if (goingTo.getAttr(XCSG.name).toString().equals("for update")) {
//								e.tag(XCSG.ControlFlowBackEdge);
//							}
//							
						}
					}else {
						e.tag("remove_edge");
						e.to().tag("remove_node");
					}
				}
			} else {
				Edge in = n.in(XCSG.ControlFlow_Edge).one();
				AtlasSet<Edge> out = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
				Node predecessor = in.from();
				Node successor = null;
				
				for (Edge e : out) {
					successor = e.to();
//					if (!e.taggedWith("src_induced_edge")) {
					if (successor.taggedWith(XCSG.ControlFlowCondition) && e.taggedWith(XCSG.ControlFlowBackEdge)) {
						n.tag("src_node");
						e.tag("src_induced_edge");
					}	
					 else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.ControlFlowCondition)) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
							
							if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
								inducedEdge.tag(XCSG.ControlFlowBackEdge);
							}
						}
						else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.Break)){
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.taggedWith(XCSG.controlFlowExitPoint)) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.taggedWith(XCSG.ControlFlowCondition) && successor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.taggedWith(XCSG.Break) && successor.taggedWith(XCSG.ControlFlowCondition)) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.taggedWith(XCSG.Break) && successor.taggedWith(XCSG.controlFlowExitPoint)){
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.taggedWith(XCSG.Break) && successor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2 && successor.taggedWith(XCSG.ControlFlowCondition)) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
							
							if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
								inducedEdge.tag(XCSG.ControlFlowBackEdge);
							}
							
						}else if (predecessor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2 && successor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2 && successor.taggedWith(XCSG.controlFlowExitPoint)) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (predecessor.in().taggedWithAny(XCSG.ControlFlow_Edge).size() >=2 && successor.taggedWith(XCSG.Break)) {
							Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
							inducedEdge.tag("src_induced_edge");
							successor.tag("src_node");
						}else if (!n.taggedWith("src_node")){
							e.tag("remove_edge");
							successor.tag("remove_node");
							n.tag("remove_node");
						}
//					}
					
				}
			}
			
		}
		
		Q removeNodes = subgraph.nodesTaggedWithAll("remove_node");
		Q removeSubGraph = subgraph.edgesTaggedWithAll("remove_edge").between(removeNodes, removeNodes);

		for (Node n : removeSubGraph.roots().eval().nodes()) {
			Node nextNode = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().to();
//					.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().to();
			while (!nextNode.taggedWith("src_node")) {
				
				AtlasSet<Edge> dagEdges = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
//				nextNode = nextNode.out("REDIRECTED_CONTROL_FLOW_BACK_EDGE").one().to();
				if (dagEdges.size() != 0) {
					nextNode = dagEdges.one().to();
				}else if (nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).size() > 0) {
					nextNode = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().to();
				}
			}
			if (nextNode.taggedWith("src_node")) {
				Edge inducedEdge = Graph.U.createEdge(n.in(XCSG.ControlFlow_Edge).one().from(), nextNode);
				inducedEdge.tag("src_induced_edge");
				nextNode.tag("src_node");
//				if (nextNode.in().taggedWithAll(XCSG.ControlFlowBackEdge).size() > 0) {
//					inducedEdge.tag(XCSG.ControlFlowBackEdge);
//				}
			}
		}
		
//		return removeSubGraph;
		return subgraph.nodes("src_node").induce(Query.universe().edges("src_induced_edge"));
	}
	
	public static void findAllSourceSubGraphs() {
		
	}
	
	public static void findAllBinarySubGraphs() {
		
	}
	
	public static void findAllSubGraphs() {
		
	}
	
	public static void exportBinarySubGraphCounts() throws IOException {
		
		String subgraphCountsPath = "/Users/RyanGoluch/Desktop/binary_induced_graph_counts.csv";
		File countsFile = new File(subgraphCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		countsWriter.write("Function Name, # If Nodes, # Loop Nodes, # Switch Nodes, # of Control Flow Nodes, Total Nodes in Subgraph\n");
		countsWriter.flush();
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			
			Graph subGraph = findSubGraph(functionName).eval();
			
			long ifNodes = subGraph.nodes().tagged(XCSG.ControlFlowIfCondition).size();
			long loopNodes = subGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			long switchNodes = subGraph.nodes().tagged(XCSG.ControlFlowSwitchCondition).size();
			long totalNodes = subGraph.nodes().size();
			long cfgNodes = totalNodes - (ifNodes + loopNodes + switchNodes);
			
			countsWriter.write(functionName + ",");
			countsWriter.write(ifNodes + "," + loopNodes + "," + switchNodes + "," + cfgNodes + "," + totalNodes + "\n");
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
		
		countsWriter.write("Function Name, # If Nodes, # Loop Nodes, # Switch Nodes, # of Control Flow Nodes, Total Nodes in Subgraph\n");
		countsWriter.flush();
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			functionName = functionName.replace("sym_", "");
			
			Graph subGraph = findSrcSubGraph(functionName).eval();
			
			long ifNodes = subGraph.nodes().tagged(XCSG.ControlFlowIfCondition).size();
			long loopNodes = subGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			long switchNodes = subGraph.nodes().tagged(XCSG.ControlFlowSwitchCondition).size();
			long totalNodes = subGraph.nodes().size();
			long cfgNodes = totalNodes - (ifNodes + loopNodes + switchNodes);
			
			countsWriter.write(functionName + ",");
			countsWriter.write(ifNodes + "," + loopNodes + "," + switchNodes + "," + cfgNodes + "," + totalNodes + "\n");
			countsWriter.flush();
		}
		
		countsWriter.close();
	}
	
	/**
	 *
	 * @throws IOException 
	 */
	
	public static void exportAllSubGraphCounts() throws IOException {
		String subgraphCountsPath = "/Users/RyanGoluch/Desktop/Masters_Work/all_induced_graph_counts_updated.csv";
		File countsFile = new File(subgraphCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		String selfLoops = "/Users/RyanGoluch/Desktop/Masters_Work/all_induced_selfloop_graph_counts_updated.csv";
		File selfLoopFile = new File(selfLoops);
		BufferedWriter selfLoopsWriter = new BufferedWriter(new FileWriter(selfLoopFile)); 
		
		String lookInto = "/Users/RyanGoluch/Desktop/binary_total_gt_src_functions.txt";
		File lookIntoFile = new File(lookInto);
		BufferedWriter lookIntoWriter = new BufferedWriter(new FileWriter(lookIntoFile));
		
		
		countsWriter.write("Function Name, # Induced Nodes (Bin), # Induced Nodes (Src), "
				+ "# Induced Edges (Bin), # Induced Edges (Src), # Loops (Bin), # Loops (Src), # Paths (Bin), # Paths (Src)\n");
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
			
			if(functionName.contains("test_")) {
				continue;
			}
			
			Graph binSubGraph = findSubGraph(functionName).eval();
			Graph srcSubGraph = findSrcSubGraph(srcFunctionName).eval();
			
			if (binSubGraph.edges().tagged("self_loop_edge").size() > 0) {
				System.out.println("Self Loop Functions: " + functionName);
				
				selfLoopsWriter.write(functionName + "\n");
				selfLoopsWriter.flush();
				
				continue;
			}
			
			Long binInducedNodes = binSubGraph.nodes().tagged("bin_node").size();
			Long binInducedEdges = binSubGraph.edges().tagged("bin_induced_edge").size();
			Long binLoopNodes = binSubGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			Long binInducedPaths = linearCounter.countPaths(Common.toQ(binSubGraph)).getPaths();
			
			Long srcInducedNodes = srcSubGraph.nodes().tagged("src_node").size();
			Long srcInducedEdges = srcSubGraph.edges().tagged("src_induced_edge").size();
			Long srcLoopNodes = srcSubGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			Long srcInducedPaths = srcCounter.countPaths(Common.toQ(srcSubGraph)).getPaths().longValue();
			
			
			countsWriter.write(functionName + ",");
			countsWriter.write(binInducedNodes + "," + srcInducedNodes + ",");
			countsWriter.write(binInducedEdges + "," + srcInducedEdges + ",");
			countsWriter.write(binLoopNodes + "," + srcLoopNodes + ",");
			countsWriter.write(binInducedPaths + "," + srcInducedPaths + "\n");
			countsWriter.flush();
			
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
		
		countsWriter.close();
		lookIntoWriter.close();
	}
	
}
