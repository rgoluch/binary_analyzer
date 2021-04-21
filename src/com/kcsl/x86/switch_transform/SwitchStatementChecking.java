package com.kcsl.x86.switch_transform;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import static com.kcsl.x86.support.SupportMethods.*;

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
	
	static String[] switchTags = {"bst_edge", "switch_edge"};
	static String[] switchNodeTags = {"switch_graph"};
	
	public static ArrayList<String> switchChecker() {
		
		ArrayList<String> switchFunctions = new ArrayList<String>();
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		int switchCount = 0;
//		System.out.println("Switch Statements: ");
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
		
//		System.out.println("Total number of switch functions: " + switchCount);
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
		
//		for (caseNode c : cases) {
////			System.out.println(c.getLineNumber());
//		}
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
		functionNode.tag("switch_function_node");
		
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
					Node tempPred = createNode(predecessor, switchNodeTags);
					tempPred.tag("switch_pred");
					
					if (predecessor.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(predecessor, tempPred);
					}
					
					createFunctionEdge(functionNode, tempPred);
					recreatedNodes.put(predecessor, tempPred);
					switchPredecessors.put(predecessor.addressBits(), tempPred);
					
					String conditionValue = null;
					if (e.hasAttr(XCSG.conditionValue)) {
						conditionValue = e.getAttr(XCSG.conditionValue).toString();
					}
					
					//Update the recreated node tracking and predecessor tracking 
					predecessorNode p = new predecessorNode(e.to(), predecessor, tempPred, conditionValue);
					switchNodeTracking.put(p, predecessor.addressBits());
					
				}
				else {
					String conditionValue = null;
					if (e.hasAttr(XCSG.conditionValue)) {
						conditionValue = e.getAttr(XCSG.conditionValue).toString();
					}
					
					//If node was already recreated, just update tracking
					recreatedCheck.tag("switch_pred");
					switchPredecessors.put(predecessor.addressBits(), recreatedCheck);
					predecessorNode p = new predecessorNode(e.to(), predecessor, recreatedCheck, conditionValue);
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
					
					tempTrue = createNode(trueEval, switchNodeTags);
					if (trueEval.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(trueEval, tempTrue);
					}
					
					if (trueEval.taggedWith(XCSG.CaseLabel) && !trueEval.taggedWith(XCSG.DefaultCaseLabel)) {
						tempTrue.tag(XCSG.CaseLabel);
					}
					
					createFunctionEdge(functionNode, tempTrue);
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
					tempDefault = createNode(e.from(), switchNodeTags);
					tempDefault.tag("switch_def");
					
					createFunctionEdge(functionNode, tempDefault);
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
				}
				
				if (recreatedCheck == null) {
					
					tempHeader = createNode(header, switchNodeTags);
					createFunctionEdge(functionNode, tempHeader);
					if (header.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(header, tempHeader);
					}
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
				}
				createSwitchEdge(null, null, tempDefault, tempHeader, switchTags);
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
					
					tempDefault = createNode(e.from(), switchNodeTags);
					createFunctionEdge(functionNode, tempDefault);
					if (e.from().taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(e.from(), tempDefault);
					}
					
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
				}
				
				if (recreatedCheck == null) {
					tempHeader = createNode(header, switchNodeTags);
					tempHeader.tag("switch_def");
					createFunctionEdge(functionNode, tempHeader);
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
				}
				createSwitchEdge(null, null, tempDefault, tempHeader, switchTags);
			}
			//Handle all other nodes in the graph
			else if (!e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition) 
					&& !e.to().taggedWith(XCSG.CaseLabel) && !e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node from = e.from();
				Node to = e.to();
				
				//Recreate the node if necessary and update the tracking
				Node tempFrom = createNode(from, switchNodeTags);
				Node tempTo = createNode(to, switchNodeTags);
				
				Node checkFrom = recreatedNodes.get(from);
				Node checkTo = recreatedNodes.get(to);

				if (checkFrom == null && checkTo == null) {
					
					createFunctionEdge(functionNode, tempFrom);
					createFunctionEdge(functionNode, tempTo);
					createSwitchEdge(null, e, tempFrom, tempTo, switchTags);
					
					recreatedNodes.put(from, tempFrom);
					recreatedNodes.put(to, tempTo);
					
					if (from.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(from, tempFrom);
					}
					if (to.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(to, tempTo);
					}
				}
				
				if (checkFrom != null && checkTo == null) {
					
					createFunctionEdge(functionNode, tempTo);
					createSwitchEdge(null, e, checkFrom, tempTo, switchTags);
					recreatedNodes.put(to, tempTo);
					
					if (to.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(to, tempTo);
					}
				}
				
				if (checkFrom == null && checkTo != null) {
					
					createFunctionEdge(functionNode, tempFrom);
					createSwitchEdge(null, e, tempFrom, checkTo, switchTags);
					recreatedNodes.put(from, tempFrom);
					
					if (from.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(from, tempFrom);
					}
				}
				
				if (checkFrom != null && checkTo != null) {
					createSwitchEdge(null, e, checkFrom, checkTo, switchTags);
				}
			}
			//Handle the case where we evaluate a non case node to case node, only want to recreate the non case node if necessary
			if (e.to().taggedWith(XCSG.CaseLabel) && !e.to().taggedWith(XCSG.DefaultCaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node cfgFrom = e.from();
				Node fromCheck = recreatedNodes.get(cfgFrom);
				Node tempCFGFrom = null;
				
				if (fromCheck == null) {
					
					tempCFGFrom = createNode(cfgFrom, switchNodeTags);
					if (cfgFrom.taggedWith(XCSG.ControlFlowCondition)) {
						addSCOperators(cfgFrom, tempCFGFrom);
					}
					
					createFunctionEdge(functionNode, tempCFGFrom);
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
						Node tempDefault = createNode(e.to(), switchNodeTags);
						createFunctionEdge(functionNode, tempDefault);
						if (e.to().taggedWith(XCSG.ControlFlowCondition)) {
							addSCOperators(e.to(), tempDefault);
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
				checkPoint.tag("case_node");
				long switchLine = getCSourceLineNumber(s);
				checkPoint.putAttr("line_number", cases.get(0).lineNumber+1);
				createFunctionEdge(functionNode, checkPoint);
				
				createSwitchEdge("false", null, cases.get(0).createdNode, checkPoint, switchTags);
				falseEdgeAdded.add(bstNodes.get(0));
				createSwitchEdge("true", null, checkPoint, cases.get(1).createdNode, switchTags);
				
				int mid = (cases.size() / 2) + 1;
				createSwitchEdge("false", null, checkPoint, cases.get(mid).createdNode, switchTags);
				int i = 0; 
				mid = cases.size() / 2;
				
				//Add false edges for cases 
				while (i < cases.size()) {	
					if (!falseEdgeAdded.contains(cases.get(i).createdNode) && cases.get(i).createdNode.out(XCSG.ControlFlow_Edge).size() < 2) {						
						if ((i == mid) || (i == cases.size() - 1)) {
							createSwitchEdge("false", null, cases.get(i).createdNode, defaultNodeTracking.get(s), switchTags);
							falseEdgeAdded.add(cases.get(i).createdNode);
						}
						else if (i < cases.size() - 1) {
							createSwitchEdge("false", null, cases.get(i).createdNode, cases.get(i+1).createdNode, switchTags);
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
						createSwitchEdge("false", null, cases.get(i - 1).createdNode, cases.get(i).createdNode, switchTags);
					}
				}
				
				Node falseEdgeToNode = defaultNodeTracking.get(s);
				createSwitchEdge("false", null, cases.get(cases.size()-1).createdNode, falseEdgeToNode, switchTags);
			}
		}

		
		//Have all predecessors point to the first case
		for (Node k : switchNodes) {
			for (predecessorNode p : switchNodeTracking.keySet()) {
				if (p.switchNode.equals(k)) {
					Node first = switchCaseRelation.get(k).get(0).createdNode;
					if (p.conditionValue != null) {
						createSwitchEdge(p.conditionValue, null, p.createdNode, first, switchTags);
					}else {
						createSwitchEdge(null, null, p.createdNode, first, switchTags);
					}
				}
			}
		}
		
		//Add fall through edges (i.e. if cases are consecutive with no break or return)
		for (Node n : caseCFGPredecessors.keySet()) {
			Node cfgPred = caseCFGPredecessors.get(n);
			Node caseAdded = casesAdded.get(n);
			createSwitchEdge(null, null, cfgPred, caseAdded, switchTags);
		}
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q switch_cfg = my_cfg(x);
		return switch_cfg.nodes("switch_graph").induce(Query.universe().edges("switch_edge"));
	}
	
	
	
	public static ArrayList<Node> bstCaseNodes(Map<Node, ArrayList<caseNode>> nodesMap, Node functionNode, Map<Node, Node> casesAdded, Map<Node, caseNode> bstSorted) {
		
		ArrayList<Node> bst = new ArrayList<Node>();
		String[] nodeTags = {"switch_graph", XCSG.ControlFlowCondition, "bst_node"};
		
		for (Node s : nodesMap.keySet()) {
			
			ArrayList<caseNode> nodes = nodesMap.get(s);
			ArrayList<caseNode> replacementList = new ArrayList<caseNode>();
			
			int l = 0;
			int r = nodes.size() - 1;
			int mid = (l + r) / 2;
			
			
			for (int j = mid; j < nodes.size(); j++) {
				//Create case condition
				Node current = nodes.get(j).getOriginalNode();
				Node caseCreate = createNode(current, nodeTags);
				caseCreate.tag("case_node");
				//Add to array for size check
				if (casesAdded.get(current) == null) {
					bst.add(caseCreate);
					
					nodes.get(j).setCreatedNode(caseCreate);
					bstSorted.put(caseCreate, nodes.get(j));
					replacementList.add(nodes.get(j));
					
					//Add to return graph
					createFunctionEdge(functionNode, caseCreate);
					
					//Set true destination
					Node trueDest = nodes.get(j).getToNode();
					
					if (trueDest.taggedWith(XCSG.CaseLabel)) {
						for (int z = 0; z < nodes.size(); z++) {
							if (nodes.get(z).originalNode.getAttr(XCSG.name).toString().contains(trueDest.getAttr(XCSG.name).toString())) {
								trueDest = nodes.get(z).toNode;
								createSwitchEdge("false", null, caseCreate, trueDest, switchTags);
							}
						}
					}
					
					trueDest.tag("bst_node");
					casesAdded.put(current, trueDest);
					createSwitchEdge("true", null, caseCreate, trueDest, switchTags);
				}
			}
			for (int i = mid-1; i >= 0; i--) {
				Node currentI = nodes.get(i).getOriginalNode();
				Node caseCreateI = createNode(currentI, nodeTags);
				caseCreateI.tag("case_node");
				
				//Add to array for size check
				if (casesAdded.get(currentI) == null) {
					bst.add(caseCreateI);
					
					nodes.get(i).setCreatedNode(caseCreateI);
					bstSorted.put(caseCreateI, nodes.get(i));
					replacementList.add(nodes.get(i));
					
					//Add to return graph
					createFunctionEdge(functionNode, caseCreateI);
					
					//Set true destination
					Node trueDest = nodes.get(i).getToNode();
					
					if (trueDest.taggedWith(XCSG.CaseLabel)) {
						for (int z = 0; z < nodes.size(); z++) {
							if (nodes.get(z).originalNode.getAttr(XCSG.name).toString().contains(trueDest.getAttr(XCSG.name).toString())) {
								trueDest = nodes.get(z).getToNode();
								createSwitchEdge("false", null, caseCreateI, trueDest, switchTags);
							}
						}
					}
					
					trueDest.tag("bst_node");
					casesAdded.put(currentI, trueDest);		
					createSwitchEdge("true", null, caseCreateI, trueDest, switchTags);
				}
			}
			
			nodesMap.replace(s, replacementList);
		}

		return bst;
	}
	
	
	//Handling the case when there are logical operators for short circuit transform
	public static void addSCOperators(Node conditional, Node createdNode) {
		
		AtlasSet<Node> containerNodes = Common.toQ(conditional).contained().nodes(XCSG.LogicalAnd, XCSG.LogicalOr).eval().nodes();
		if (containerNodes.size() > 0) {
			for (Node n : containerNodes) {
				Iterable<String> containerTags = n.tagsI();
				Node dataNode = Graph.U.createNode();
				String dName = n.getAttr(XCSG.name).toString();
				dataNode.putAttr(XCSG.name, dName);
				for (String t : containerTags) {
					dataNode.tag(t);
				}
				dataNode.tag("switch_graph");
				dataNode.tag("data_node");
				Edge containerEdge = Graph.U.createEdge(createdNode, dataNode);
				containerEdge.tag(XCSG.Contains);
				containerEdge.tag("switch_edge");
			}
		}
	}
	
	public static void createFunctionEdge(Node functionNode, Node created) {
		Edge functionEdge = Graph.U.createEdge(functionNode, created);
		functionEdge.tag(XCSG.Contains);
	}
	
	public static void createSwitchEdge(String condVal, Edge e, Node f, Node t, String[] transformTags) {
		Edge cfgEdge = Graph.U.createEdge(f, t);
		cfgEdge.tag(XCSG.ControlFlow_Edge);
		for (String s : transformTags) {
			cfgEdge.tag(s);
		}
		
		if (condVal != null) {
			cfgEdge.putAttr(XCSG.conditionValue, condVal);
			if (condVal.contains("true")) {
				cfgEdge.putAttr(XCSG.name, "true");
			}else if (condVal.contains("false")){
				cfgEdge.putAttr(XCSG.name, "false");
			}else if (condVal.contains("default")) {
				cfgEdge.putAttr(XCSG.name, "default");
			}
		}else if (e != null) {
			if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
				cfgEdge.tag(XCSG.ControlFlowBackEdge);
			}
			
			if (e.hasAttr(XCSG.conditionValue)) {
				if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
					cfgEdge.putAttr(XCSG.conditionValue, "true");
					cfgEdge.putAttr(XCSG.name, "true");
				}else {
					cfgEdge.putAttr(XCSG.conditionValue, "false");
					cfgEdge.putAttr(XCSG.name, "false");
				}
			}
		}
		
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
		private String conditionValue;
		
		public predecessorNode(Node s, Node p, Node c, String v) {
			this.switchNode = s;
			this.createdNode = c;
			this.predNode = p;
			this.conditionValue = v;
		}
	
	}
	
}
