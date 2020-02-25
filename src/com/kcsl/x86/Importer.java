package com.kcsl.x86;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;
//import org.radare.r2pipe.R2Pipe;
//import com.kcsl.paths;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.DisplayUtil;
import com.ensoftcorp.open.commons.algorithms.LoopIdentification;
import com.ensoftcorp.open.commons.ui.utilities.DisplayUtils;
//import com.kcsl.paths.counting.TopDownDFMultiplicitiesPathCounter.*;
//import com.kcsl.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.algorithms.counting.DFSPathCounter;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;
import com.se421.paths.algorithms.*;
import com.se421.paths.algorithms.PathCounter.CountingResult;

public class Importer {

	protected static final String resultsPath = "/Users/RyanGoluch/Desktop/My_Results.csv";
	
	protected static final String headers = "Function Name,numPaths (NonLinear),additions (NonLinear),numPaths (Linear),additions (Linear)\n";
	
	private static ArrayList<Node> function_nodes = new ArrayList<Node>();
	
	public static void main() throws FileNotFoundException {
		// HashMap of Node for further access
		Map<String,Node> nodeMap = new HashMap<String,Node>();
		
		//read in and parse .dot files from dot_graphs dir
		String path = "/Users/RyanGoluch/Desktop/Research/kothari_490/com.kcsl.x86/dot_graphs";
		File dir = new File(path);
		File[] dirList = dir.listFiles();
		int count = 0; 
		for(File dot : dirList) {
			if (dot.exists()) {
				count++;
//				System.out.println("Count: " +count+" Function: "+dot.getName());
				Node functionName = Graph.U.createNode();
				functionName.putAttr(XCSG.name, "sym_"+dot.getName().replace(".dot", ""));
				functionName.tag(XCSG.Function);
				functionName.tag("binary_function");
				function_nodes.add(functionName);
				Scanner s = new Scanner(dot);

				//
				
				while(s.hasNextLine()) {
					String data = s.nextLine();
					if(data.contains("[URL")) {
						//Create control flow nodes with labels
						Node n = Graph.U.createNode(); 
						String addr = data.subSequence(2, 12).toString();
						String label = data.split("label=")[1];
						label = label.replace("\"", "");
						label = label.replace("]", "");
						label = label.replace("\\l", "\n");
						n.putAttr(XCSG.name, label);
						
						//Map all control flow nodes to function container
						Edge temp = Graph.U.createEdge(functionName, n);
						temp.tag(XCSG.Contains);
						nodeMap.put(addr, n);
					}
					else if(data.contains("->")) {
						data = data.replaceAll("\\s+", "");
//						System.out.println(data);
						//Extract the addresses of the from and to nodes in DOT file
						String from = data.split("->")[0];
						from = from.replaceAll("\"", "");
						String temp = data.split("->")[1];
						String to = temp.split("\\[color")[0];
						to = to.replaceAll("\"", "");
//						System.out.print(to);
						
						//Create the Atlas nodes and add necessary tags
						Node fromNode = nodeMap.get(from);
						fromNode.tag(XCSG.ControlFlow_Node);
						fromNode.tag("my_node");
						
						//Handling exit nodes for test files in test directory
						if(nodeMap.get(to) == null) {
							Node exitNode = Graph.U.createNode();
							exitNode.putAttr(XCSG.name, to);
							exitNode.tag(XCSG.ControlFlow_Node);
							exitNode.tag("my_node");
							
							Edge x = Graph.U.createEdge(fromNode, exitNode);
							x.tag(XCSG.ControlFlow_Edge);
							x.tag("my_edge");
						}else {
							Node toNode = nodeMap.get(to);
							toNode.tag(XCSG.ControlFlow_Node);
							toNode.tag("my_node");
							
							Edge e = Graph.U.createEdge(fromNode, toNode);
							e.tag(XCSG.ControlFlow_Edge);
							e.tag("my_edge");
						}
					}
					
				}
				s.close();
			}
			
		}
		
		
		//create a new node
		//XCSG.name, name of function (differentiate from source)
		//tag as XCSG.Function
		//Node fn = Graph.U.createNode();
		//create edge between fn and all other control flow nodes
		//tag it as XCSG.Contains
	}
	
	public static Q my_function(String name) {
		Q f = Query.universe().nodes(XCSG.Function);
		Q found = f.selectNode(XCSG.name, name);
		return found;
	}
	
	public static Q my_cfg(Q f) {
		return f.contained().nodes(XCSG.ControlFlow_Node).induce(Query.universe().edges(XCSG.ControlFlow_Edge));
	}
	
	public static void export_counts() throws IOException {

			File results = new File(resultsPath);
			BufferedWriter resultsWriter = new BufferedWriter(new FileWriter(results));
			resultsWriter.write(headers);
			DFSPathCounter nonLinearCounter = new DFSPathCounter();
			MultiplicitiesPathCounter linearCounter = new MultiplicitiesPathCounter();
			
			// We will now generate the results for all the functions in the graph database.
			// It is assumed that you have XINU mapped into Atlas before you run this code.
//			Q app = SetDefinitions.app();
		 	Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		 			//app.nodes(XCSG.Function).nodesTaggedWithAll("my_function");
			for(Node function : functions.eval().nodes()) {
				
				if(function.getAttr(XCSG.name).toString().contains("test_libString")) {
					continue;
				}
				
				Q temp = Common.toQ(function);
				Q c = my_cfg(temp);
//				DisplayUtil.displayGraph(c.eval());
				System.out.println(function.getAttr(XCSG.name));
				if (c.eval().nodes().size() > 1) {
					LoopIdentification l = new LoopIdentification(c.eval(), c.roots().eval().nodes().one());
				}
				
//				CountingResult nonLinear = nonLinearCounter.countPaths(c);
				CountingResult linear = linearCounter.countPaths(c);
				
				// function name
				resultsWriter.write(function.getAttr(XCSG.name) + ",");
				
				// number of paths according to nonLinear algorithm
//				resultsWriter.write(nonLinear.getPaths() + ",");
				
				// number of additions by nonLinear algorithm
//				resultsWriter.write(nonLinear.getAdditions() + ",");
				
				// number of paths according to linear algorithm
				resultsWriter.write(linear.getPaths() + ",");
				
				// number of additions by linear algorithm
				resultsWriter.write(linear.getAdditions() + "\n");
				
				// flushing the buffer
				resultsWriter.flush();
			}
			
			resultsWriter.close();
	}
}
