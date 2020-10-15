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

		Q c = subGraphGenerator(name);
		
		//Get all the nodes tagged with control flow conditions that would cause some form
		//of branching in the graph
		Q ifNodes = c.nodesTaggedWithAll(XCSG.ControlFlowIfCondition);		
		Q loopNodes = c.nodesTaggedWithAll(XCSG.ControlFlowLoopCondition);
		Q switchNodes = c.nodesTaggedWithAll(XCSG.ControlFlowSwitchCondition);
		
		//Find and generate the sub graph that is bounded above by if statements
		Q if_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, loopNodes);
		Q if_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, switchNodes);
		Q if_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, ifNodes);
		
		Q if_subgraph = if_and_loops.union(if_and_switch).union(if_and_if);
		
		//Find and generate the subgraph that is bounded above by loop conditions
		Q loops_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, ifNodes);
		Q loops_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, switchNodes);
		Q loops_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, loopNodes);
		
		Q loop_subgraph = loops_and_if.union(loops_and_switch).union(loops_and_loops);
		
		//Find and generate the subgraph that is bounded above by switch statements
		Q switch_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, ifNodes);
		Q switch_and_loop = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, ifNodes);
		Q switch_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, ifNodes);
		
		Q switch_subgraph = switch_and_if.union(switch_and_loop).union(switch_and_switch);
		
		Q subgraph = if_subgraph.union(loop_subgraph).union(switch_subgraph);
		
		for(Node n : subgraph.eval().nodes()) {
					
			if(!n.taggedWith(XCSG.ControlFlowCondition)) {
				Edge in = n.in(XCSG.ControlFlow_Edge).one();
				Edge out = n.out(XCSG.ControlFlow_Edge).one();
				
				Node predecessor = in.from();
				Node sucessor = out.to();
				
				Edge inducedEdge = Graph.U.createEdge(predecessor, sucessor);
				inducedEdge.tag("binary_induced_edge");
			} else if (n.taggedWith(XCSG.ControlFlowCondition)) {
				AtlasSet<Edge> outgoing = n.out(XCSG.ControlFlow_Edge);
				
				for(Edge e : outgoing) {
					e.tag("binary_induced_edge");
				}
			}
		}
		
		return subgraph.nodes(XCSG.ControlFlowCondition).induce(Query.universe().edges("binary_induced_edge"));
	}

	/**
	 * 
	 * @param name
	 * @return
	 */
	
	public static Q findSrcSubGraph(String name) {
		//Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		Q subgraph = subGraphGenerator(name);

		for(Node n : subgraph.eval().nodes()) {
			
			if (!n.taggedWith(XCSG.ControlFlowCondition)) {
							
				Edge in = n.in(XCSG.ControlFlow_Edge).one();
				AtlasSet<Edge> out = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
//						n.out(XCSG.ControlFlow_Edge);
//				AtlasSet<Edge> backEdges = n.out(XCSG.ControlFlowBackEdge);
//				if (backEdges.size() > 0) {
//					System.out.println("backedges: "+ backEdges.one());
//					out.add(backEdges.one());
//				}
				Node predecessor = in.from();
				Node successor = null;
				
				for (Edge e : out) {
					successor = e.to();
					if (successor.taggedWith(XCSG.ControlFlowCondition) && predecessor.taggedWith(XCSG.ControlFlowCondition) && !successor.taggedWith("src_node")) {
						Edge inducedEdge = Graph.U.createEdge(predecessor, successor);
						inducedEdge.tag("src_induced_edge");
						successor.tag("src_node");
						if (n.taggedWith("remove_node")) {
							n.untag("remove_node");
							in.untag("remove_edge");
						}
					}else if (!successor.taggedWith(XCSG.ControlFlowCondition) && !successor.taggedWith(XCSG.controlFlowExitPoint)){
						e.tag("remove_edge");
						successor.tag("remove_node");
					}
				}
			}else if (n.taggedWith(XCSG.ControlFlowCondition)) {
				AtlasSet<Edge> outgoing = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
//				AtlasSet<Edge> backEdges = n.out(XCSG.ControlFlowBackEdge);
//				if(backEdges.size() > 0) {
//					outgoing.add(backEdges.one());
//
//				}
//				System.out.println("outgoing: "+outgoing.toString());
				for(Edge e : outgoing) {
					if (e.to().taggedWith(XCSG.ControlFlowCondition) && !e.to().taggedWith("src_node")) {
						e.tag("src_induced_edge");
						e.to().tag("src_node");
					}else if (!e.to().taggedWith(XCSG.controlFlowExitPoint)) {
						e.tag("remove_edge");
						e.to().tag("remove_node");
					}
				}
			} 
			
		}
		
		Q removeNodes = subgraph.nodesTaggedWithAll("remove_node");
		Q removeSubGraph = subgraph.edgesTaggedWithAll("remove_edge").between(removeNodes, removeNodes);
		
		for (Node n : removeSubGraph.roots().eval().nodes()) {
			
			Node nextNode = n.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().to();
			while (!nextNode.taggedWith(XCSG.ControlFlowCondition)) {
				
				AtlasSet<Edge> dagEdges = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge);
//				nextNode = nextNode.out("REDIRECTED_CONTROL_FLOW_BACK_EDGE").one().to();
				if (dagEdges.size() != 0) {
					nextNode = dagEdges.one().to();
				}else if (nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).size() > 0) {
					nextNode = nextNode.out().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().to();
				}else if (nextNode.taggedWith(XCSG.controlFlowExitPoint)){
					nextNode = n.in().taggedWithAny(XCSG.ControlFlow_Edge, XCSG.ControlFlowBackEdge).one().from();
					System.out.println("Check function: "+name);
					System.out.println(nextNode.getAttr(XCSG.name).toString());
//					break;
				}
			}
			if (nextNode.taggedWith(XCSG.ControlFlowCondition) && !nextNode.taggedWith("src_node") && nextNode.in().tagged("src_induced_edge").size() == 0 ) {
				
//				Edge incoming = nextNode.in("REDIRECTED_CONTROL_FLOW_BACK_EDGE").one();
//				if (incoming != null) {
//					Edge inducedEdge = Graph.U.createEdge(n.in(XCSG.ControlFlow_Edge).one().from(), nextNode);
//					inducedEdge.tag("src_induced_edge");
//				}else {
					Edge inducedEdge = Graph.U.createEdge(n.in(XCSG.ControlFlow_Edge).one().from(), nextNode);
					inducedEdge.tag("src_induced_edge");
//				}
				
			}
		}
		
//		return removeSubGraph;
		return subgraph.nodes(XCSG.ControlFlowCondition).induce(Query.universe().edges("src_induced_edge"));
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
	
	public static void exportAllSubGraphCounts() throws IOException {
		String subgraphCountsPath = "/Users/RyanGoluch/Desktop/all_induced_graph_counts.csv";
		File countsFile = new File(subgraphCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		String lookInto = "/Users/RyanGoluch/Desktop/binary_total_gt_src_functions.txt";
		File lookIntoFile = new File(lookInto);
		BufferedWriter lookIntoWriter = new BufferedWriter(new FileWriter(lookIntoFile));
		
		countsWriter.write("Function Name, # If Nodes (Bin), # If Nodes (Src), # Loop Nodes (Bin), # Loop Nodes (Src), # Switch Nodes (Bin), # Switch Nodes (Src), "
				+ "# of Control Flow Nodes (Bin), # of Control Flow Nodes (Src), Total Nodes in Subgraph (Bin), Total Nodes in Subgraph (Src)\n");
		countsWriter.flush();
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		
		long bin_total_gt_src = 0;
		long bin_total_lt_src = 0;
		long bin_total_eq_src = 0;
		
		for(Node function : functions.eval().nodes()) {
			String functionName = function.getAttr(XCSG.name).toString();
			String srcFunctionName = functionName.replace("sym_", "");
			
			if(functionName.contains("test")) {
				continue;
			}
			
			Graph binSubGraph = findSubGraph(functionName).eval();
			Graph srcSubGraph = findSrcSubGraph(srcFunctionName).eval();
			
			Long binIfNodes = binSubGraph.nodes().tagged(XCSG.ControlFlowIfCondition).size();
			Long binLoopNodes = binSubGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			Long binSwitchNodes = binSubGraph.nodes().tagged(XCSG.ControlFlowSwitchCondition).size();
			Long binTotalNodes = binSubGraph.nodes().size();
			Long binCFGNodes = binTotalNodes - (binIfNodes + binLoopNodes + binSwitchNodes);
			
			Long srcIfNodes = srcSubGraph.nodes().tagged(XCSG.ControlFlowIfCondition).size();
			Long srcLoopNodes = srcSubGraph.nodes().tagged(XCSG.ControlFlowLoopCondition).size();
			Long srcSwitchNodes = srcSubGraph.nodes().tagged(XCSG.ControlFlowSwitchCondition).size();
			Long srcTotalNodes = srcSubGraph.nodes().size();
			Long srcCFGNodes = srcTotalNodes - (srcIfNodes + srcLoopNodes + srcSwitchNodes);
			
			
			countsWriter.write(functionName + ",");
			countsWriter.write(binIfNodes + "," + srcIfNodes + ",");
			countsWriter.write(binLoopNodes + "," + srcLoopNodes + ",");
			countsWriter.write(binSwitchNodes + "," + srcSwitchNodes + ",");
			countsWriter.write(binCFGNodes + "," + srcCFGNodes + ",");
			countsWriter.write(binTotalNodes + "," + srcTotalNodes + "\n");
			countsWriter.flush();
			
			if (binTotalNodes > srcTotalNodes) {
				bin_total_gt_src +=1;
				lookIntoWriter.write(functionName + "\n");
				lookIntoWriter.flush();
			}
			if (binTotalNodes < srcTotalNodes) {
				bin_total_lt_src +=1;
			}
			if (binTotalNodes == srcTotalNodes) {
				bin_total_eq_src +=1;
			}
		}
		
		countsWriter.write("\n");
		countsWriter.write("Bin Total > Src Total, Bin Total < Src Total, Bin Total == Src Total\n");
		countsWriter.write(bin_total_gt_src + "," + bin_total_lt_src + "," + bin_total_eq_src);
		countsWriter.flush();
		
		countsWriter.close();
		lookIntoWriter.close();
	}
	
}
