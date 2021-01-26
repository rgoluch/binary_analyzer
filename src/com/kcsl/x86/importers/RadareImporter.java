package com.kcsl.x86.importers;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import static com.kcsl.x86.support.SupportMethods.*;
import static com.kcsl.x86.Importer.*;

/**
 * 
 * @author RyanGoluch
 *
 */

public class RadareImporter {
	
	private static ArrayList<Node> function_nodes = new ArrayList<Node>();
	
	/**
	 * 
	 * @throws FileNotFoundException
	 */
	
	public static void import_radare() throws FileNotFoundException {
			
			// HashMap of Node for further access
			Map<String,Node> nodeMap = new HashMap<String,Node>();
			
			//read in and parse .dot files from dot_graphs dir
			String path = "/Users/RyanGoluch/Desktop/Research/kothari_490/com.kcsl.x86/dot_graphs";
			File dir = new File(path);
			File[] dirList = dir.listFiles(new FilenameFilter() {
				@Override
				public boolean accept(File dir, String name) {
					return name.endsWith(".dot");
				}
			});
			
			int count = 0;
			boolean cmp = true;
			for(File dot : dirList) {
				ArrayList<Node> indexedNodes = new ArrayList<Node>();
				
				//check to make sure that this condition is needed
				if (dot.exists()) {
					Node functionName = Graph.U.createNode();
					functionName.putAttr(XCSG.name, "sym_"+dot.getName().replace(".dot", ""));
					functionName.tag(XCSG.Function);
					functionName.tag("binary_function");
					functionName.tag("radare_function");
					
					
					//Creation of consolidated exit node
					//Comment out lines 68-75 for original exit points
					Node exit = Graph.U.createNode();
					exit.putAttr(XCSG.name, "binary exit");
					exit.tag("my_node");
					exit.tag("bin_node");
					exit.tag("single_exit");
					exit.tag(XCSG.controlFlowExitPoint);
					exit.tag(XCSG.ControlFlow_Node);
					Edge functionExit = Graph.U.createEdge(functionName, exit);
					functionExit.tag(XCSG.Contains);
					
					function_nodes.add(functionName);
					Scanner s = new Scanner(dot);
					
					while(s.hasNextLine()) {
						
						String data = s.nextLine();
						
						if(data.contains("[URL")) {
							
							//Create control flow nodes with labels
							Node n = Graph.U.createNode(); 
							n.tag(XCSG.ControlFlow_Node);
							n.tag("my_node");
							
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
							
							//Extract the addresses of the from and to nodes in DOT file
							String from = data.split("->")[0];
							from = from.replaceAll("\"", "");
							
							String temp = data.split("->")[1];
							String to = temp.split("\\[color")[0];
							to = to.replaceAll("\"", "");
							
							//Get the edge color to properly mark true and false edges later on
							String color = temp.split("\\[color=")[1];
							color = color.replaceAll("];", "");
							color = color.replaceAll("\"", "");
							
							//Create the Atlas nodes and add necessary tags
							Node fromNode = nodeMap.get(from);
							
							if (functionName.getAttr(XCSG.name).equals("sym_strcmp") && cmp) {
								fromNode.tag(XCSG.controlFlowRoot);
								cmp = false;
							}
							
							indexedNodes.add(fromNode);
							
							//Handling exit nodes for test files in test directory
							if(nodeMap.get(to) == null) {
								
								Node exitNode = Graph.U.createNode();
								exitNode.putAttr(XCSG.name, to);
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
								
								//Mark true and false edges based on dot file edge color
								if (color.contentEquals("#13a10e")) {
									e.putAttr(XCSG.conditionValue, true);
								}
								else if (color.contentEquals("#c50f1f")) {
									e.putAttr(XCSG.conditionValue, false);
								}
//								else if (color.contentEquals("#0037da")) {
//									e.tag(XCSG.ControlFlowBackEdge);
//								}
						
								if(from.contains(to)) {
									
//									Node root = Graph.U.createNode();
//									root.putAttr(XCSG.name, "root");
//									root.tag(XCSG.ControlFlow_Node);
//									root.putAttr(XCSG.controlFlowRoot, "root");
//									
//									Edge t = Graph.U.createEdge(functionName, root);
//									t.tag(XCSG.Contains);
//									
//									Edge root_to_loop = Graph.U.createEdge(root, fromNode);
//									root_to_loop.tag(XCSG.ControlFlow_Edge);
									
									fromNode.tag("self_loop_node");
									fromNode.tag(XCSG.Loop);
									fromNode.tag(XCSG.ControlFlowLoopCondition);
									
									Node loopBody = Graph.U.createNode();
									loopBody.tag(XCSG.ControlFlow_Node);
									loopBody.tag("my_node");
									loopBody.putAttr(XCSG.name, fromNode.getAttr(XCSG.name).toString());

									Edge containEdge = Graph.U.createEdge(functionName, loopBody);
									containEdge.tag(XCSG.Contains);
									
//									System.out.println(fromNode.getAttr(XCSG.name).toString());
									String conditionVal = null;
									if (e.hasAttr(XCSG.conditionValue)) {
										conditionVal = e.getAttr(XCSG.conditionValue).toString();

									}
									
									Graph.U.delete(e);
									
//									Edge originalLoopBody = from.oneOut("self_loop_edge");
//									originalLoopBody.untag(XCSG.ControlFlowBackEdge);
									
									Edge headerToBody = Graph.U.createEdge(fromNode, loopBody);
									headerToBody.tag(XCSG.ControlFlow_Edge);
									headerToBody.putAttr(XCSG.conditionValue, conditionVal);
									
//									AtlasSet<Edge> conditionValues = fromNode.out().taggedWithAll(XCSG.ControlFlow_Edge);
//									for (Edge z : conditionValues) {
//										if(z.hasAttr(XCSG.conditionValue)) {
//											if(z.getAttr(XCSG.conditionValue).toString() == "false") {
//												headerToBody.putAttr(XCSG.conditionValue, "true");
//											}else if(z.getAttr(XCSG.conditionValue).toString() == "true") {
//												headerToBody.putAttr(XCSG.conditionValue, "false");
//											}
//										}
//									}
									
									Edge bodyToHeader = Graph.U.createEdge(loopBody, fromNode);
//									bodyToHeader.tag("bin_induced_edge");
									bodyToHeader.tag(XCSG.ControlFlowBackEdge);
									
//									e.tag("self_loop_edge");
//									e.tag(XCSG.ControlFlowBackEdge);
									count +=1;
									
								}
							}
						}
						
					}
					s.close();
				}
				
			}
			
			//Go through all of the nodes that are created and tag all loops and conditionals
			Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
			
			for(Node function : functions.eval().nodes()) {
				String name = function.getAttr(XCSG.name).toString();
				//Toggle which line is commented out depending on if single return or original returns
				//being used
//				tag_binary_exits(name);
//				if (name.contains("strcmp")) {
					tag_binary_single_exits(name);
					tag_binary_branches(name);
					tag_binary_loops(name);
					tag_binary_ifs(name);
//				}
				
			}
			
			
			System.out.println(count);
			//create a new node
			//XCSG.name, name of function (differentiate from source)
			//tag as XCSG.Function
			//Node fn = Graph.U.createNode();
			//create edge between fn and all other control flow nodes
			//tag it as XCSG.Contains
		}
		
}
