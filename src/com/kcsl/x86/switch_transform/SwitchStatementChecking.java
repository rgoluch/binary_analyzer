package com.kcsl.x86.switch_transform;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class SwitchStatementChecking {

	
	public static ArrayList<String> switchChecker() {
		
		ArrayList<String> switchFunctions = new ArrayList<String>();
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		int switchCount = 0;
		System.out.println("Switch Statements: ");
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			String srcName = functionName.substring(4);
			
			Q function = my_function(srcName);
			Q c = my_cfg(function);
			for (Node n : c.eval().nodes()) {
				if (n.taggedWith(XCSG.ControlFlowSwitchCondition)) {
					switchCount++;
					switchFunctions.add(srcName);
				}
			}
		}
		
		System.out.println("Total number of switch functions: " + switchCount);
		return switchFunctions;
	}
	
	public static ArrayList<caseNode> caseSorter(ArrayList<caseNode> cases) {
		for (int i = 0; i < cases.size(); i++) {
			for (int j = i+1; j < cases.size(); j++) {
				caseNode x = cases.get(i);
				caseNode y = cases.get(j);
				long temp = cases.get(i).getLineNumber();
				long current = cases.get(j).getLineNumber();
				if (temp > current) {
					cases.set(i,y);
					cases.set(j, x);
				}
			}
		}
		
		for (caseNode c : cases) {
			System.out.println(c.getLineNumber());
		}
		return cases;
	}
	
	public static Q switchTransform(String name, Q c) {
		
		//Get the original source CFG
//		Q f = my_function(name);	
//		Q c = my_cfg(f);
		
		AtlasSet<Node> switchNodes = c.eval().nodes().tagged(XCSG.ControlFlowSwitchCondition);
		if (switchNodes.size() == 0) {
			return c;
		}
		
		//Set up for new function node for returned CFG
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "switch_transform_"+name);
		functionNode.tag(XCSG.Function);
		functionNode.tag("switch_graph");
		
		//Keep track of what nodes have already been recreated for final graph
		Map<Node,Node> recreatedNodes = new HashMap<Node,Node>();
		//Keep track of the case nodes as we find them
		ArrayList<caseNode> caseNodes = new ArrayList<caseNode>();
		//Keep track of all nodes that have an edge to a switch header
		Map<Integer,Node> switchPredecessors = new HashMap<Integer,Node>();
		//Keep track of the CFG nodes that proceed each of the case nodes for continuation edges
		Map<Node, Node> caseCFGPredecessors = new HashMap<Node, Node>();
		//Key is the predecessor node that is created, value is the address bits of predecessor
		Map<predecessorNode,Integer> switchNodeTracking = new HashMap<predecessorNode,Integer>();
		//Used to keep track of the default nodes for each switch block
		Map<Node,Node> defaultNodeTracking = new HashMap<Node,Node>();

		
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			
			//First check to see if are going to a switch node
			if (e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				
				Node predecessor = e.from();
				Node recreatedCheck = recreatedNodes.get(predecessor);
				
				//Do not want to inadvertently retain a switch node
				if(e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
					continue;
				}
				
				if (recreatedCheck == null) {
					Node tempPred = Graph.U.createNode();
					tempPred.putAttr(XCSG.name, predecessor.getAttr(XCSG.name).toString());
					tempPred.tag("switch_graph");
					tempPred.tag("switch_pred");
					tempPred.tag(XCSG.ControlFlow_Node);
					
					if (predecessor.taggedWith(XCSG.ControlFlowCondition)) {
						tempPred.tag(XCSG.ControlFlowCondition);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempPred);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(predecessor, tempPred);
					switchPredecessors.put(predecessor.addressBits(), tempPred);
					
					//Update the recreated node tracking and predecessor tracking 
					predecessorNode p = new predecessorNode(e.to(), predecessor, tempPred);
					switchNodeTracking.put(p, predecessor.addressBits());
					
				}
				else {
					
					//If node was already recreated, just update tracking
					recreatedCheck.tag("switch_pred");
					switchPredecessors.put(predecessor.addressBits(), recreatedCheck);
					
					predecessorNode p = new predecessorNode(e.to(), predecessor, recreatedCheck);
					switchNodeTracking.put(p, predecessor.addressBits());
				}
			}
			//Handle the case where CFG nodes are case and non-case node
			else if (e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.DefaultCaseLabel)) {
				Node trueEval = e.to();
				Node recreatedCheck = recreatedNodes.get(trueEval);
				Node tempTrue = null;
				
				//Recreate the to node if necessary and then update the tracking
				if (recreatedCheck == null) {
					tempTrue = Graph.U.createNode();
					tempTrue.putAttr(XCSG.name, trueEval.getAttr(XCSG.name).toString());
					tempTrue.tag("switch_graph");
					tempTrue.tag(XCSG.ControlFlow_Node);
					
					if (trueEval.taggedWith(XCSG.ControlFlowCondition)) {
						tempTrue.tag(XCSG.ControlFlowCondition);
					}
					
					if (trueEval.taggedWith(XCSG.CaseLabel) && !trueEval.taggedWith(XCSG.DefaultCaseLabel)) {
						tempTrue.tag(XCSG.CaseLabel);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempTrue);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(trueEval, tempTrue);
				}
				else {
					tempTrue = recreatedCheck;
				}
				
				//Keep track of which switch node points to each case, so we need to find the switch node
				AtlasSet<Edge> inEdges = e.from().in(XCSG.ControlFlow_Edge);
				Node switchToCaseNode = null;
				for (Edge i : inEdges) {
					if (i.hasAttr(XCSG.conditionValue)) {
						if (!i.getAttr(XCSG.conditionValue).toString().contains("default")) {
							switchToCaseNode = i.from();
						}
					}
				}
				
				//Track the case nodes 
				long l = getCSourceLineNumber(e.from());
				caseNode x = new caseNode(e.from(), l, tempTrue);
				x.setSwitchNode(switchToCaseNode);
				caseNodes.add(x);
				continue;
			}
			//Handle the case where the from node is a default case, this should not become a branch node 
			else if (e.from().taggedWith(XCSG.DefaultCaseLabel)) {
				Node header = e.to();
				
				Node recreatedCheck = recreatedNodes.get(header);
				Node recreatedFromCheck = recreatedNodes.get(e.from());
				Node tempDefault = null;
				Node tempHeader = null;
				
				//Recreate the node if necessary and update the tracking
				if (recreatedFromCheck == null) {
					tempDefault = Graph.U.createNode();
					
					tempDefault.putAttr(XCSG.name, e.from().getAttr(XCSG.name).toString());
					tempDefault.tag("switch_graph");
					tempDefault.tag("switch_def");
					tempDefault.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempDefault);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
				}
				
				if (recreatedCheck == null) {
					tempHeader = Graph.U.createNode();
					
					tempHeader.putAttr(XCSG.name, header.getAttr(XCSG.name).toString());
					tempHeader.tag("switch_graph");
					tempHeader.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempHeader);
					e1.tag(XCSG.Contains);
					
					if (header.taggedWith(XCSG.ControlFlowCondition)) {
						tempHeader.tag(XCSG.ControlFlowCondition);
					}
					if (header.taggedWith(XCSG.controlFlowExitPoint)) {
						tempHeader.tag(XCSG.controlFlowExitPoint);
					}
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
				}
				
				Edge defaultEdge = Graph.U.createEdge(tempDefault, tempHeader);
				defaultEdge.tag(XCSG.ControlFlow_Edge);
				defaultEdge.tag("switch_edge");
			}
			//Handle the case where the end of one case points to a default case with no break or return 
			else if (e.to().taggedWith(XCSG.DefaultCaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node header = e.to();
				
				Node recreatedCheck = recreatedNodes.get(header);
				Node recreatedFromCheck = recreatedNodes.get(e.from());
				Node tempDefault = null;
				Node tempHeader = null;
				
				//Recreate the node if necessary and update tracking
				if (recreatedFromCheck == null) {
					tempDefault = Graph.U.createNode();
					
					tempDefault.putAttr(XCSG.name, e.from().getAttr(XCSG.name).toString());
					tempDefault.tag("switch_graph");
					tempDefault.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempDefault);
					e1.tag(XCSG.Contains);
					
					if (e.from().taggedWith(XCSG.ControlFlowCondition)) {
						tempDefault.tag(XCSG.ControlFlowCondition);
					}
					if (e.from().taggedWith(XCSG.controlFlowExitPoint)) {
						tempDefault.tag(XCSG.controlFlowExitPoint);
					}
					
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
				}
				
				if (recreatedCheck == null) {
					tempHeader = Graph.U.createNode();
					
					tempHeader.putAttr(XCSG.name, header.getAttr(XCSG.name).toString());
					tempHeader.tag("switch_graph");
					tempHeader.tag("switch_def");
					tempHeader.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempHeader);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
				}
				
				Edge defaultEdge = Graph.U.createEdge(tempDefault, tempHeader);
				defaultEdge.tag(XCSG.ControlFlow_Edge);
				defaultEdge.tag("switch_edge");
			}
			//Handle all other nodes in the graph
			else if (!e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition) 
					&& !e.to().taggedWith(XCSG.CaseLabel) && !e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node from = e.from();
				Node to = e.to();
				
				Node tempFrom = Graph.U.createNode();
				Node tempTo = Graph.U.createNode();
				
				//Recreate the node if necessary and update the tracking
				tempFrom.putAttr(XCSG.name, from.getAttr(XCSG.name).toString());
				tempFrom.tag("switch_graph");
				tempFrom.tag(XCSG.ControlFlow_Node);
				tempTo.putAttr(XCSG.name, to.getAttr(XCSG.name).toString());
				tempTo.tag("switch_graph");
				tempTo.tag(XCSG.ControlFlow_Node);
				
				if (from.taggedWith(XCSG.ControlFlowCondition)) {
					tempFrom.tag(XCSG.ControlFlowCondition);
				}
				if (from.taggedWith(XCSG.controlFlowExitPoint)) {
					tempFrom.tag(XCSG.controlFlowExitPoint);
				}
				if (to.taggedWith(XCSG.ControlFlowCondition)) {
					tempTo.tag(XCSG.ControlFlowCondition);
				}
				if (to.taggedWith(XCSG.controlFlowExitPoint)) {
					tempTo.tag(XCSG.controlFlowExitPoint);
				}
				
				Node checkFrom = recreatedNodes.get(from);
				Node checkTo = recreatedNodes.get(to);
				Edge tempEdge = null;

				if (checkFrom == null && checkTo == null) {
					Edge e1 = Graph.U.createEdge(functionNode, tempFrom);
					e1.tag(XCSG.Contains);
					
					Edge e2 = Graph.U.createEdge(functionNode, tempTo);
					e2.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, tempTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
					
					recreatedNodes.put(from, tempFrom);
					recreatedNodes.put(to, tempTo);
				}
				
				if (checkFrom != null && checkTo == null) {
					Edge e2 = Graph.U.createEdge(functionNode, tempTo);
					e2.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(checkFrom, tempTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
					
					recreatedNodes.put(to, tempTo);
				}
				
				if (checkFrom == null && checkTo != null) {
					Edge e2 = Graph.U.createEdge(functionNode, tempFrom);
					e2.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, checkTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
					
					recreatedNodes.put(from, tempFrom);
				}
				
				if (checkFrom != null && checkTo != null) {
					tempEdge = Graph.U.createEdge(checkFrom, checkTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
				}
				
				if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
					tempEdge.tag(XCSG.ControlFlowBackEdge);
				}
				
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						tempEdge.putAttr(XCSG.conditionValue, "true");
					}else {
						tempEdge.putAttr(XCSG.conditionValue, "false");
					}
				}
			}
			//Handle the case where we evaluate a non case node to case node, only want to recreate the non case node if necessary
			if (e.to().taggedWith(XCSG.CaseLabel) && !e.to().taggedWith(XCSG.DefaultCaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node cfgFrom = e.from();
				Node fromCheck = recreatedNodes.get(cfgFrom);
				Node tempCFGFrom = null;
				
				if (fromCheck == null) {
					tempCFGFrom = Graph.U.createNode();
					tempCFGFrom.putAttr(XCSG.name, cfgFrom.getAttr(XCSG.name).toString());
					tempCFGFrom.tag("switch_graph");
					tempCFGFrom.tag(XCSG.ControlFlow_Node);
					
					if (cfgFrom.taggedWith(XCSG.ControlFlowCondition)) {
						tempCFGFrom.tag(XCSG.ControlFlowCondition);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempCFGFrom);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(cfgFrom, tempCFGFrom);
					caseCFGPredecessors.put(e.to(), tempCFGFrom);
				}
				else {
					tempCFGFrom = fromCheck;
					caseCFGPredecessors.put(e.to(), tempCFGFrom);
				}
			}
		}
		
		//Keep track of the cases that have been added to the final graph
		Map<Node, Node> casesAdded = new HashMap<Node, Node>();
		//Mapping of the created case node to the respective caseNode object
		Map<Node, caseNode> bstToSortedNodes = new HashMap<Node, caseNode>();
		//Mapping of each switch node to all of its respective cases
		Map<Node, ArrayList<caseNode>> switchCaseRelation = new HashMap<Node, ArrayList<caseNode>>();
		
		//Fill switchCaseRelation mapping
		for (Node s : switchNodes) {
			ArrayList<caseNode> tempList = new ArrayList<caseNode>();
			
			for (caseNode b : caseNodes) {
				if (b.switchNode.equals(s)) {
					tempList.add(b);
				}
			}
			
			switchCaseRelation.put(s, tempList);
		}
		
		//Bubble sort each switch's cases and update the mapping
		for (Node g : switchCaseRelation.keySet()) {
			ArrayList<caseNode> a = switchCaseRelation.get(g);
			a = caseSorter(a);
			switchCaseRelation.replace(g, a);
		}
		
		//Create the case node branches and add the true edges. 
		ArrayList<Node> bstNodes = bstCaseNodes(switchCaseRelation, functionNode, casesAdded, bstToSortedNodes);
		
		//Fill the default node mapping to know which node in the CFG is the default to node for each switch node
		for (Node n : switchNodes) {
			for (Edge e : n.out(XCSG.ControlFlow_Edge)) {
				if (e.getAttr(XCSG.conditionValue).toString().contains("default") && !e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
					Node toNodeChecking = null;
					
					for (Node r : recreatedNodes.keySet()) {
						if (e.to().equals(r)) {
							toNodeChecking = recreatedNodes.get(r);
							break;
						}
					}
					
					if (toNodeChecking == null) {
						Node tempDefault = Graph.U.createNode();
						tempDefault.putAttr(XCSG.name, e.to().getAttr(XCSG.name).toString());
						tempDefault.tag("switch_graph");
						tempDefault.tag(XCSG.ControlFlow_Node);
						
						Edge containerEdge = Graph.U.createEdge(functionNode, tempDefault);
						containerEdge.tag(XCSG.Contains);
						
						if (e.to().taggedWith(XCSG.ControlFlowCondition)) {
							tempDefault.tag(XCSG.ControlFlowCondition);
						}
						if (e.to().taggedWith(XCSG.controlFlowExitPoint)) {
							tempDefault.tag(XCSG.controlFlowExitPoint);
						}
						
						toNodeChecking = tempDefault;
					}
					
					defaultNodeTracking.put(n, toNodeChecking);
				}
				else if (e.getAttr(XCSG.conditionValue).toString().contains("default") && e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
					
					ArrayList<caseNode> sortedCases = switchCaseRelation.get(n);
					
					int mid = (int) e.to().out(XCSG.ControlFlow_Edge).size()/2;
					Node toNodeChecking = e.to();
					
					if (toNodeChecking.taggedWith("switch_graph")) {
						toNodeChecking.untag("switch_graph");
					}

					caseNode s = sortedCases.get(mid);
					if(toNodeChecking.equals(s.switchNode)) {
						toNodeChecking = s.createdNode;
					}
					defaultNodeTracking.put(n, toNodeChecking);
				}
			}
		}
		
		
		ArrayList<Node> falseEdgeAdded = new ArrayList<Node>();
		for (Node s : switchCaseRelation.keySet()) {
			
			ArrayList<caseNode> cases = switchCaseRelation.get(s);
			
			//Add in checkpoint node for switch nodes with more than 3 cases
			if (cases.size() > 3) {
				Node checkPoint = Graph.U.createNode();
				checkPoint.putAttr(XCSG.name, "direction checkpoint");
				checkPoint.tag(XCSG.ControlFlowCondition);
				checkPoint.tag("switch_graph");
				checkPoint.tag("bst_node");
				checkPoint.tag("check");
				
				Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
				checkPointEdge.tag(XCSG.Contains);
				
				Edge firstFalseEdge = Graph.U.createEdge(cases.get(0).createdNode, checkPoint);
				firstFalseEdge.tag(XCSG.ControlFlow_Edge);
				firstFalseEdge.tag("switch_edge");
				firstFalseEdge.tag("bst_edge");
				firstFalseEdge.putAttr(XCSG.conditionValue, false);
				firstFalseEdge.putAttr(XCSG.name, "false");
				falseEdgeAdded.add(bstNodes.get(0));
				
				Edge checkPointTrue = Graph.U.createEdge(checkPoint, cases.get(1).createdNode);
				checkPointTrue.tag(XCSG.ControlFlow_Edge);
				checkPointTrue.tag("switch_edge");
				checkPointTrue.tag("bst_edge");
				checkPointTrue.putAttr(XCSG.conditionValue, true);
				checkPointTrue.putAttr(XCSG.name, "true");
				
				int mid = (cases.size() / 2) + 1;
				
				Edge checkPointFalse = Graph.U.createEdge(checkPoint, cases.get(mid).createdNode);
				checkPointFalse.tag(XCSG.ControlFlow_Edge);
				checkPointFalse.tag("switch_edge");
				checkPointFalse.tag("bst_edge");
				checkPointFalse.putAttr(XCSG.conditionValue, false);
				checkPointFalse.putAttr(XCSG.name, "false");
				
				int i = 0; 
				mid = cases.size() / 2;
				
				//Add false edges for cases 
				while (i < cases.size()) {	
					if (!falseEdgeAdded.contains(cases.get(i).createdNode) && cases.get(i).createdNode.out(XCSG.ControlFlow_Edge).size() < 2) {						
						if ((i == mid) || (i == cases.size() - 1)) {
							Edge falseEdge = Graph.U.createEdge(cases.get(i).createdNode, defaultNodeTracking.get(s));
							falseEdge.putAttr(XCSG.conditionValue, false);
							falseEdge.tag(XCSG.ControlFlow_Edge);
							falseEdge.tag("bst_edge");
							falseEdge.tag("switch_edge");
							falseEdge.putAttr(XCSG.name, "false");
							falseEdgeAdded.add(cases.get(i).createdNode);
						}
						else if (i < cases.size() - 1) {
							Edge falseEdge = Graph.U.createEdge(cases.get(i).createdNode, cases.get(i+1).createdNode);
							falseEdge.putAttr(XCSG.conditionValue, false);
							falseEdge.tag(XCSG.ControlFlow_Edge);
							falseEdge.tag("bst_edge");
							falseEdge.tag("switch_edge");
							falseEdge.putAttr(XCSG.name, "false");
							falseEdgeAdded.add(cases.get(i).createdNode);
						}
					}
					i++;
				}
			}
			else {
				//Add false edges for and switch node with fewer than 4 cases
				for (int i = 1; i < cases.size(); i++) {
					if (cases.get(i-1).createdNode.out(XCSG.ControlFlow_Edge).size() < 2) {
						Edge falseEdge = Graph.U.createEdge(cases.get(i - 1).createdNode, cases.get(i).createdNode);
						falseEdge.putAttr(XCSG.conditionValue, false);
						falseEdge.tag(XCSG.ControlFlow_Edge);
						falseEdge.tag("bst_edge");
						falseEdge.tag("switch_edge");
						falseEdge.putAttr(XCSG.name, "false");
					}
				}
				
				Node falseEdgeToNode = defaultNodeTracking.get(s);
				
				Edge falseEdge = Graph.U.createEdge(cases.get(cases.size()-1).createdNode, falseEdgeToNode);
				falseEdge.putAttr(XCSG.conditionValue, false);
				falseEdge.tag(XCSG.ControlFlow_Edge);
				falseEdge.tag("bst_edge");
				falseEdge.tag("switch_edge");
				falseEdge.putAttr(XCSG.name, "false");
			}
		}

		
		//Have all predecessors point to the first case
		for (Node k : switchNodes) {
			for (predecessorNode p : switchNodeTracking.keySet()) {
				if (p.switchNode.equals(k)) {
					Node first = switchCaseRelation.get(k).get(0).createdNode;
					Edge predEdge = Graph.U.createEdge(p.createdNode, first);
					predEdge.tag(XCSG.ControlFlow_Edge);
					predEdge.tag("switch_edge");
				}
			}
		}
		
		//Add fall through edges (i.e. if cases are consecutive with no break or return)
		for (Node n : caseCFGPredecessors.keySet()) {
			Node cfgPred = caseCFGPredecessors.get(n);
			Node caseAdded = casesAdded.get(n);
			
			Edge cfgPredEdge = Graph.U.createEdge(cfgPred, caseAdded);
			cfgPredEdge.tag(XCSG.ControlFlow_Edge);
			cfgPredEdge.tag("switch_edge");
		}
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q switch_cfg = my_cfg(x);
		return switch_cfg.nodes("switch_graph").induce(Query.universe().edges("switch_edge"));
	}
	
	
	
	public static ArrayList<Node> bstCaseNodes(Map<Node, ArrayList<caseNode>> nodesMap, Node functionNode, Map<Node, Node> casesAdded, Map<Node, caseNode> bstSorted) {
		ArrayList<Node> bst = new ArrayList<Node>();
		
		for (Node s : nodesMap.keySet()) {
			
			ArrayList<caseNode> nodes = nodesMap.get(s);
			ArrayList<caseNode> replacementList = new ArrayList<caseNode>();
			
			int l = 0;
			int r = nodes.size() - 1;
			int mid = (l + r) / 2;
			
			
			for (int j = mid; j < nodes.size(); j++) {
				Node current = nodes.get(j).getOriginalNode();
				Node caseCreate = Graph.U.createNode();
				
				//Create the case condition
				caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
				caseCreate.tag(XCSG.ControlFlowCondition);
				caseCreate.tag("switch_graph");
				caseCreate.tag("bst_node");
				
				//Add to array for size check
				if (casesAdded.get(current) == null) {
					bst.add(caseCreate);
					
					nodes.get(j).setCreatedNode(caseCreate);
					bstSorted.put(caseCreate, nodes.get(j));
					replacementList.add(nodes.get(j));
					
					//Add to return graph
					Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
					containerEdge.tag(XCSG.Contains);
					
					//Set true destination
					Node trueDest = nodes.get(j).getToNode();
					
					if (trueDest.taggedWith(XCSG.CaseLabel)) {
						for (int z = 0; z < nodes.size(); z++) {
							if (nodes.get(z).originalNode.getAttr(XCSG.name).toString().contains(trueDest.getAttr(XCSG.name).toString())) {
								trueDest = nodes.get(z).toNode;
								
								Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
								trueEdge.tag("bst_edge");
								trueEdge.tag("switch_edge");
								trueEdge.putAttr(XCSG.conditionValue, false);
								trueEdge.tag(XCSG.ControlFlow_Edge);
								trueEdge.putAttr(XCSG.name, "false");
							}
						}
					}
					
					trueDest.tag("bst_node");
					casesAdded.put(current, trueDest);
					
					Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
					trueEdge.tag("bst_edge");
					trueEdge.tag("switch_edge");
					trueEdge.putAttr(XCSG.conditionValue, true);
					trueEdge.tag(XCSG.ControlFlow_Edge);
					trueEdge.putAttr(XCSG.name, "true");
				}
			}
			for (int i = mid-1; i >= 0; i--) {
				Node currentI = nodes.get(i).getOriginalNode();
				Node caseCreateI = Graph.U.createNode();
				
				//Create the case condition
				caseCreateI.putAttr(XCSG.name, currentI.getAttr(XCSG.name).toString());
				caseCreateI.tag(XCSG.ControlFlowCondition);
				caseCreateI.tag("switch_graph");
				caseCreateI.tag("bst_node");
				
				//Add to array for size check
				if (casesAdded.get(currentI) == null) {
					bst.add(caseCreateI);
					
					nodes.get(i).setCreatedNode(caseCreateI);
					bstSorted.put(caseCreateI, nodes.get(i));
					replacementList.add(nodes.get(i));
					
					//Add to return graph
					Edge containerEdge = Graph.U.createEdge(functionNode, caseCreateI);
					containerEdge.tag(XCSG.Contains);
					
					//Set true destination
					Node trueDest = nodes.get(i).getToNode();
					
					if (trueDest.taggedWith(XCSG.CaseLabel)) {
						for (int z = 0; z < nodes.size(); z++) {
							if (nodes.get(z).originalNode.getAttr(XCSG.name).toString().contains(trueDest.getAttr(XCSG.name).toString())) {
								trueDest = nodes.get(z).getToNode();
								
								Edge trueEdge = Graph.U.createEdge(caseCreateI, trueDest);
								trueEdge.tag("bst_edge");
								trueEdge.tag("switch_edge");
								trueEdge.putAttr(XCSG.conditionValue, false);
								trueEdge.tag(XCSG.ControlFlow_Edge);
								trueEdge.putAttr(XCSG.name, "false");

							}
						}
					}
					
					trueDest.tag("bst_node");
					casesAdded.put(currentI, trueDest);
					
					Edge trueEdge = Graph.U.createEdge(caseCreateI, trueDest);
					trueEdge.tag("bst_edge");
					trueEdge.tag("switch_edge");
					trueEdge.putAttr(XCSG.conditionValue, true);
					trueEdge.tag(XCSG.ControlFlow_Edge);
					trueEdge.putAttr(XCSG.name, "true");

				}
			}
			
			nodesMap.replace(s, replacementList);
		}

		return bst;
	}
	
	private static class caseNode{
		private Node originalNode;
		private long lineNumber; 
		private Node toNode;
		private Node createdNode;
		private Node switchNode;
		
		public caseNode(Node n, long l, Node t) {
			this.lineNumber = l;
			this.originalNode = n;
			this.originalNode.tag(XCSG.ControlFlowCondition);
			this.originalNode.tag("bst_node");
			this.toNode = t;
		}
		
		public Node getToNode() {
			return this.toNode;
		}
		
		public Node getOriginalNode() {
			return this.originalNode;
		}
		
		public long getLineNumber() {
			return this.lineNumber;
		}
		
		public void setCreatedNode(Node n) {
			this.createdNode = n;
		}
		
		public void setSwitchNode(Node n) {
			this.switchNode = n;
		}
	
	}
	
	private static class predecessorNode{
		private Node switchNode;
		private Node predNode; 
		private Node createdNode;
		
		public predecessorNode(Node s, Node p, Node c) {
			this.switchNode = s;
			this.createdNode = c;
			this.predNode = p;
		}
	
	}
	
	private static Long getCSourceLineNumber(Node node) {
		long lineNumber = -1;
		if (node.hasAttr(XCSG.sourceCorrespondence)) {
			SourceCorrespondence sc = (SourceCorrespondence) node.getAttr(XCSG.sourceCorrespondence);
			if (sc != null) {
				lineNumber = sc.startLine;
			}
		}
		return lineNumber;
	}
	
}
