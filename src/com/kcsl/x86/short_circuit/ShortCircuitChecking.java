package com.kcsl.x86.short_circuit;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.kcsl.paths.counting.TopDownDFMultiplicitiesPathCounter;
import com.se421.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;

public class ShortCircuitChecking {
	
	protected static final String OR = "||";
	protected static final String AND = "&&";
	protected static final String LAST = "sc_end";

	
	/**
	 * 
	 * @param cfg
	 * @return
	 */
	
	public static scInfo scChecker(Q cfg) {
		
		AtlasSet<Node> conditions = cfg.eval().nodes().tagged(XCSG.ControlFlowCondition);
		ArrayList<String> ordering = new ArrayList<String>();
		scInfo scCount = null;
		
		for (Node n : conditions) {
			AtlasSet<Node> toCheck = Common.toQ(n).contained().nodes(XCSG.LogicalOr, XCSG.LogicalAnd).eval().nodes();
			
			if (toCheck.size() > 0) {
				long and = Common.toQ(n).contained().nodes(XCSG.LogicalAnd).eval().nodes().size();
				long or = Common.toQ(n).contained().nodes(XCSG.LogicalOr).eval().nodes().size();
				scCount = new scInfo(toCheck.size(), and, or);
			}
			
			for (Node x : toCheck) {
				ordering.add(x.getAttr(XCSG.name).toString());
			}
		}
		
		return scCount;
	}
	
	
	/**
	 * 
	 * @param name
	 * @return
	 */
	
	public static Q scTransform(String name) {
		
		//Get the original source CFG
		Q f = my_function(name);	
		Q c = my_cfg(f);
		
		
		//Set up for new function node for returned CFG
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "sc_transform_"+name);
		functionNode.tag(XCSG.Function);
		functionNode.tag("sc_graph");

		//Variables to hold nodes that potentially have complex conditions, the nodes with complex conditions,
		//and the ordering of those complex conditions
		AtlasSet<Node> conditionNodes = c.eval().nodes().tagged(XCSG.ControlFlowCondition);
		ArrayList<Node> scNodes = new ArrayList<Node>();
		
		//Finding the complex conditions
		for (Node n : conditionNodes) {
			AtlasSet<Node> toCheck = Common.toQ(n).contained().nodes(XCSG.LogicalOr, XCSG.LogicalAnd).eval().nodes();
			if (toCheck.size() > 0) {
				scNodes.add(n);
				n.tag("sc_node");
			}
		}
		
		Node trueDest = null;
		Node falseDest = null;
		
		//Tagging all non-complex condition nodes for creation in the final CFG
		for (Node n : c.eval().nodes()) {
			if(!scNodes.contains(n)) {
				n.tag("sc_graph");
			}
		}
		
		//Tagging all edges for creation in the final CFG
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			e.tag("sc_edge");
		}
		
		
		Map<Node,Node> addedToGraph = new HashMap<Node,Node>();
		ArrayList<Node> scPredecessors = new ArrayList<Node>();
		Map<Integer,Node> predMap = new HashMap<Integer,Node>();
		ArrayList<predecessorNode> loopBackTails = new ArrayList<predecessorNode>();
		Map<Node,Node> loopBackHeaderMap = new HashMap<Node,Node>();
		ArrayList<predecessorNode> edgeCreated = new ArrayList<predecessorNode>(); 

		ArrayList<Node> scHeaders = new ArrayList<Node>();

		
		//Create nodes for the new graph that will be returned 
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			
			//Handling the case of the complex condition predecessor that needs to point to the new 
			//simple condition
			if (scNodes.contains(e.to()) && !e.from().taggedWith("sc_node")) {
				Node tempSCPred = Graph.U.createNode();
				String predName = e.from().getAttr(XCSG.name).toString();
				
				tempSCPred.putAttr(XCSG.name, predName);
				tempSCPred.tag(XCSG.ControlFlow_Node);
				tempSCPred.tag("sc_graph");
				
				if (e.from().taggedWith(XCSG.ControlFlowCondition)) {
					tempSCPred.tag(XCSG.ControlFlowCondition);
				}
				
//				if (!e.taggedWith(XCSG.ControlFlowBackEdge)) {
//					tempSCPred.tag("sc_pred");
//
//				}
//				e.from().tag("sc_pred");
				
				//Check to make sure the from node hasn't already been created. 
				//If it has, handle the special case of the edge being a loopback edge since that node is not a predecessor node
				Node checkingPred = addedToGraph.get(e.from());
				
				//If predecessor node is a conditional, then we want to add the condition value on the edge
				String edgeValue = null;
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						edgeValue = "true";
					}else {
						edgeValue = "false";
					}
				}
				
				//Case where node was created and is the predecessor
				if (checkingPred != null && !e.taggedWith(XCSG.ControlFlowBackEdge)) {
					scPredecessors.add(checkingPred);
					predMap.put(checkingPred.addressBits(), e.to());
					predecessorNode p = new predecessorNode(e.from().addressBits(), e.to().addressBits(), checkingPred, edgeValue);
					edgeCreated.add(p);
				} 
				//Case where node was created and edge is a loopback edge
				else if (checkingPred != null && e.taggedWith(XCSG.ControlFlowBackEdge)) {
					predecessorNode p = new predecessorNode(e.from().addressBits(), e.to().addressBits(), checkingPred, edgeValue);
					loopBackTails.add(p);
					loopBackHeaderMap.put(checkingPred, e.to());
				}
				//Case where node hasn't been created yet, still need to handle loopback edge and predecessor checks
				else if (checkingPred == null) {
					Edge eToPred = Graph.U.createEdge(functionNode, tempSCPred);
					eToPred.tag(XCSG.Contains);
					addedToGraph.put(e.from(), tempSCPred);
					
					if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
						predecessorNode p = new predecessorNode(e.from().addressBits(), e.to().addressBits(), tempSCPred, edgeValue);
						loopBackTails.add(p);
						loopBackHeaderMap.put(tempSCPred, e.to());
					}else {
						scPredecessors.add(tempSCPred);
						predMap.put(tempSCPred.addressBits(), e.to());
						predecessorNode p = new predecessorNode(e.from().addressBits(), e.to().addressBits(), tempSCPred, edgeValue);
						edgeCreated.add(p);
					}
				}
			}
			
			else if (scNodes.contains(e.from()) && e.to().taggedWith("sc_graph")) {
				Node tempSingle = Graph.U.createNode();
				String singleName = e.to().getAttr(XCSG.name).toString();
				
				tempSingle.putAttr(XCSG.name, singleName);
				tempSingle.tag(XCSG.ControlFlow_Node);
				tempSingle.tag("sc_graph");
				
				if (e.to().taggedWith(XCSG.ControlFlowCondition)) {
					tempSingle.tag(XCSG.ControlFlowCondition);
				}
				
				if (e.to().taggedWith(XCSG.controlFlowExitPoint)) {
					tempSingle.tag(XCSG.controlFlowExitPoint);
//					tempSingle.tag("src_exit");
				}
				
				//Check to make sure the node hasn't already been created so we don't make duplicated nodes
				Node checkingSuccessor = addedToGraph.get(e.to());
				if (checkingSuccessor == null) {
					Edge eToSingle = Graph.U.createEdge(functionNode, tempSingle);
					eToSingle.tag(XCSG.Contains);
					addedToGraph.put(e.to(), tempSingle);
				}
			}
			//Handling all other control flow nodes
			else if (e.from().taggedWith("sc_graph") && e.to().taggedWith("sc_graph")) {
				Node tempFrom = Graph.U.createNode();
				Node tempTo = Graph.U.createNode();
				
				String fromName = e.from().getAttr(XCSG.name).toString();
				String toName = e.to().getAttr(XCSG.name).toString();
				
				tempFrom.putAttr(XCSG.name, fromName);
				tempFrom.tag(XCSG.ControlFlow_Node);
				tempFrom.tag("sc_graph");
				
				if (e.from().taggedWith(XCSG.ControlFlowCondition)) {
					tempFrom.tag(XCSG.ControlFlowCondition);
				}
				
				if (e.from().taggedWith(XCSG.controlFlowExitPoint)) {
					tempFrom.tag(XCSG.controlFlowExitPoint);
//					tempFrom.tag("src_exit");
				}
				
				if (e.to().taggedWith(XCSG.controlFlowExitPoint)) {
					tempTo.tag(XCSG.controlFlowExitPoint);
//					tempTo.tag("src_exit");
				}
				
				tempTo.putAttr(XCSG.name, toName);
				tempTo.tag(XCSG.ControlFlow_Node);
				tempTo.tag("sc_graph");
				
				if (e.to().taggedWith(XCSG.ControlFlowCondition)) {
					tempTo.tag(XCSG.ControlFlowCondition);
				}
				
				//Check to make sure the node hasn't already been created so we don't make duplicated nodes
				Node checkingResultFrom  = addedToGraph.get(e.from());
				Node checkingResultTo = addedToGraph.get(e.to());
				Edge tempEdge = null;
				
				if (checkingResultFrom == null && checkingResultTo == null) {
					Edge eFrom = Graph.U.createEdge(functionNode, tempFrom);
					eFrom.tag(XCSG.Contains);
					
					Edge eTo = Graph.U.createEdge(functionNode, tempTo);
					eTo.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, tempTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
					
					addedToGraph.put(e.from(), tempFrom);
					addedToGraph.put(e.to(), tempTo);
				}
				else if (checkingResultFrom != null && checkingResultTo == null) {
					Edge eTo = Graph.U.createEdge(functionNode, tempTo);
					eTo.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(checkingResultFrom, tempTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
					
					addedToGraph.put(e.to(), tempTo);
				}
				else if (checkingResultFrom == null && checkingResultTo != null) {
					Edge eFrom = Graph.U.createEdge(functionNode, tempFrom);
					eFrom.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, checkingResultTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
					
					addedToGraph.put(e.from(), tempFrom);
				}
				else if (checkingResultFrom != null && checkingResultTo != null) {
					tempEdge = Graph.U.createEdge(checkingResultFrom, checkingResultTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
				}
				
				if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
					tempEdge.tag(XCSG.ControlFlowBackEdge);
				}
				
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						tempEdge.putAttr(XCSG.conditionValue, true);
						tempEdge.putAttr(XCSG.name, "true");
					}else {
						tempEdge.putAttr(XCSG.conditionValue, false);
						tempEdge.putAttr(XCSG.name, "false");
					}
				}
			}
			
			if (e.from().taggedWith("sc_node") && e.to().taggedWith("sc_node")) {
				e.to().tag("nested_sc");
			}
		}
		
		//Move nested SC nodes to the beginning of the array to be processed first
		//in order to have initial true and false destinations
		for (int r = 0; r < scNodes.size(); r++) {
			Node current = scNodes.get(r);
//			int lastNonNested = 0;
			for (int s = r + 1; s < scNodes.size(); s++) {
				Node next = scNodes.get(s);
				
				if(!current.taggedWith("nested_sc") && next.taggedWith("nested_sc")) {
					Node temp = current; 
//					lastNonNested = r;
					scNodes.set(r, next);
					scNodes.set(s, temp);
					current = scNodes.get(r);
				}
//				else if (current.taggedWith("nested_sc") && next.taggedWith("nested_sc")) {
//					Node temp = scNodes.get(lastNonNested);
////					lastNonNested = r;
//					scNodes.set(r, next);
//					scNodes.set(s, temp);
//				}
			}
		}
		
		//Processing each node that could cause short circuiting
		for (Node x : scNodes) {
			AtlasSet<Edge> outEdges = x.out().tagged(XCSG.ControlFlow_Edge);
			Edge o1 = null;
			Edge o2 = null;
			
			for (Edge e : outEdges) {
				if (o1 == null) {
					o1 = e;
				}else {
					o2 = e;
				}
			}
			
			//Finding the true and false edge destinations depending on if there are 
			//nested or non-nested complex conditionals
			if (o1.getAttr(XCSG.conditionValue).toString().contains("true")) {
				
				if (o1.to().taggedWith("nested_sc") && !o2.to().taggedWith("nested_sc")) {
					for (Node t : scHeaders) {
						if (o1.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							trueDest = t;
						}
					}
					falseDest = addedToGraph.get(o2.to());
				}else if (o2.to().taggedWith("nested_sc") && !o1.to().taggedWith("nested_sc")) {
					for (Node t : scHeaders) {
						if (o2.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							falseDest = t;
						}
					}
					trueDest = addedToGraph.get(o1.to());
				}else if (o1.to().taggedWith("nested_sc") && o2.to().taggedWith("nested_sc")) {
					for (Node t : scHeaders) {
						if (o1.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							trueDest = t;
						}
						if (o2.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							falseDest = t;
						}
					}
				}
				else {
					trueDest = addedToGraph.get(o1.to());
					falseDest = addedToGraph.get(o2.to());
				}
			}else {
				if (o1.to().taggedWith("nested_sc") && !o2.to().taggedWith("nested_sc")) {
					for (Node t : scHeaders) {
						if (o1.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							falseDest = t;
						}
					}
					trueDest = addedToGraph.get(o2.to());
				}else if (o2.to().taggedWith("nested_sc") && !o1.to().taggedWith("nested_sc")) {
					for (Node t : scHeaders) {
						if (o2.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							trueDest = t;
						}
					}
					falseDest = addedToGraph.get(o1.to());
				}else if (o1.to().taggedWith("nested_sc") && o2.to().taggedWith("nested_sc")) {
					for (Node t : scHeaders) {
						if (o1.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							falseDest = t;
						}
						if (o2.to().getAttr(XCSG.name).toString().contains(t.getAttr(XCSG.name).toString())) {
							trueDest = t;
						}
					}
				}
				else {
					falseDest = addedToGraph.get(o1.to());
					trueDest = addedToGraph.get(o2.to());
				}
			}
			
			//Getting the order of the conditions in the original node
			AtlasSet<Node> toCheck = Common.toQ(x).contained().nodes(XCSG.LogicalOr, XCSG.LogicalAnd).eval().nodes();
			ArrayList<String> ordering = new ArrayList<String>();
			for (Node q : toCheck) {
				ordering.add(q.getAttr(XCSG.name).toString());
			}

			//Getting all information from original node for new nodes in final graph
			scNode[] nodes = createScNodes(ordering, x);
			ArrayList<Node> scNodesInGraph = new ArrayList<Node>();
							
			for(int j = 0; j < nodes.length; j++) {
				
				if (nodes[j] == null) {
					System.out.println("Macro Condition: " + name);
					return null;
				}
				
				if (trueDest == null || falseDest == null) {
					System.out.println("null destination issue: " + name);
					return null;
				}
				
				//Creation of new branch nodes for final graph
				Node temp1 = Graph.U.createNode();
				temp1.putAttr(XCSG.name, nodes[j].getCondition());
				temp1.tag(XCSG.ControlFlowCondition);
				temp1.tag("sc_graph");
				scNodesInGraph.add(temp1);
				
				//If this is the first node, being created it needs to have all predecessor nodes pointing to it 
				//and have any loopback edges coming to it for loops with complex conditions
				if (j == 0) {					
					temp1.tag("sc_header");
					scHeaders.add(temp1);
					
					for(predecessorNode p : edgeCreated) {
						Node predSCNode = predMap.get(p.getAddedNode().addressBits());
						
						if (predSCNode.getAttr(XCSG.name).toString().contains(nodes[j].getCondition()) && p.getToAddr() == x.addressBits() && !p.getEdge()) {
							Edge predEdge = Graph.U.createEdge(p.getAddedNode(), temp1);
							predEdge.tag(XCSG.ControlFlow_Edge);
							predEdge.tag("sc_edge");
							predEdge.tag("sc_pred_edge");
							p.toggleEdge();
							
							if (p.conditionValue != null) {
								predEdge.putAttr(XCSG.conditionValue, p.conditionValue);
								predEdge.putAttr(XCSG.name, p.conditionValue.toString());
							}
						}
					}
					
					for (predecessorNode b : loopBackTails) {
						Node l = loopBackHeaderMap.get(b.getAddedNode());
						
						if (l.getAttr(XCSG.name).toString().contains(nodes[j].getCondition()) && b.getToAddr() == x.addressBits() && !b.getEdge()) {
							Edge backEdge = Graph.U.createEdge(b.getAddedNode(), temp1);
							backEdge.tag(XCSG.ControlFlowBackEdge);
							backEdge.tag("sc_back_edge");
							backEdge.tag("sc_edge");
							b.toggleEdge();
							
							if (b.conditionValue != null) {
								backEdge.putAttr(XCSG.conditionValue, b.conditionValue);
							}
						}
					}
				}
				Edge e1 = Graph.U.createEdge(functionNode, temp1);
				e1.tag(XCSG.Contains);
			}
			
			
			//Setting the destination nodes for the true and false edges of the nodes created
			for (int m = 0; m < scNodesInGraph.size(); m++) {
				scNode checking = nodes[m];
				Node checkingNode = scNodesInGraph.get(m);
		
				if(checking.getOperator().contains(LAST)) {
					checking.setTrueDest(checkingNode, trueDest);
					checking.setFalseDest(checkingNode, falseDest);
				}
			}
			
			for (int m = scNodesInGraph.size()-1; m >= 0; m--) {
				scNode checking = nodes[m];
				Node checkingNode = scNodesInGraph.get(m);
				
				if(checking.getOperator().contains(AND)) {
					checking.setTrueDest(checkingNode, scNodesInGraph.get(m+1));
					checking.setFalseDest(checkingNode, falseDest);
//					nodes[m+1].getFalseDest()
				}
				if(checking.getOperator().contains(OR)) {
					checking.setFalseDest(checkingNode, scNodesInGraph.get(m+1));
					checking.setTrueDest(checkingNode, nodes[m+1].getTrueDest());
				}
			}
		}
		

		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q sc_cfg = my_cfg(x);
		return sc_cfg.nodes("sc_graph").induce(Query.universe().edges("sc_edge"));
	}
	
	
	/**
	 * 
	 * @param ordering
	 * @param x
	 * @return
	 */
	
	public static scNode[] createScNodes(ArrayList<String> ordering, Node x) {

		scNode[] conditions = new scNode[ordering.size()+1];
		int j = 0; 
		int k = 0;
		
		String name = x.getAttr(XCSG.name).toString();
		String[] parts = name.split(" ");
		String updatedName[] = x.getAttr(XCSG.name).toString().split("&&|\\|\\|");
		
		for (int p = 0; p < parts.length - 1; p++) {
			String toCheck = parts[p];
			if (updatedName[k].contains(toCheck) && parts[p+1].contains(AND)) {					
				scNode tempSCNode = new scNode(updatedName[k], AND, x.addressBits());
				conditions[j] = tempSCNode;
				j++;
				k++;
			}
			else if (updatedName[k].contains(toCheck) && parts[p+1].contains(OR)) {					
				scNode tempSCNode = new scNode(updatedName[k], OR, x.addressBits());
				conditions[j] = tempSCNode;
				j++;
				k++;
			}

		}
		
		scNode temp = new scNode(updatedName[k], LAST, x.addressBits());
		conditions[conditions.length-1] = temp;

		return conditions;
	}
	
	
	private static class scNode{
		private String condition;
		private String operator; 
		private Node truDest; 
		private Node falsDest; 
		private int address; 
		
		public scNode(String c, String o, int i) {
			this.condition = c;
			this.operator = o;
			this.address = i;
		}
		
		public String getCondition() {
			return this.condition;
		}
		
		public String getOperator() {
			return this.operator;
		}
		
		public void setTrueDest(Node temp1, Node temp2) {
			this.truDest = temp2;
			
			Edge tempTrue = Graph.U.createEdge(temp1, temp2);
			tempTrue.tag(XCSG.ControlFlow_Edge);
			tempTrue.putAttr(XCSG.conditionValue, true);
			tempTrue.putAttr(XCSG.name, "true");
			tempTrue.tag("sc_edge");
			tempTrue.tag("sc_edge_testing");
		}
		
		public Node getTrueDest() {
			return this.truDest;
		}
		
		public void setFalseDest(Node temp1, Node temp2) {
			this.falsDest = temp2;
			
			Edge tempTrue = Graph.U.createEdge(temp1, temp2);
			tempTrue.tag(XCSG.ControlFlow_Edge);
			tempTrue.putAttr(XCSG.conditionValue, false);
			tempTrue.putAttr(XCSG.name, "false");
			tempTrue.tag("sc_edge");
			tempTrue.tag("sc_edge_testing");
		}
		
		public Node getFalseDest() {
			return this.falsDest;
		}
	}
	
	
	private static class scInfo{
		private long conditions; 
		private long ands;
		private long ors;
		
		public scInfo(long c, long a, long o) {
			this.conditions = c; 
			this.ands = a; 
			this.ors = o;
		}
		
		public long getConditions() {
			return this.conditions;
		}
		
		public long getAnds() {
			return this.ands;
		}
		
		public long getOrs() {
			return this.ors;
		}
	}
	
	private static class predecessorNode{
		private int fromAddr;
		private int toAddr;
		private Node addedNode;
		private boolean edgeAdded;
		private String conditionValue;
		
		public predecessorNode(int f, int t, Node n, String value) {
			this.fromAddr = f;
			this.toAddr = t;
			this.addedNode = n;
			this.edgeAdded = false;
			this.conditionValue = value;
		}
		
		public int getFromAddr() {
			return this.fromAddr;
		}
		
		public int getToAddr() {
			return this.toAddr;
		}
		
		public Node getAddedNode() {
			return this.addedNode;
		}
		
		public void toggleEdge() {
			this.edgeAdded = true;
		}
		
		public boolean getEdge() {
			return this.edgeAdded;
		}
	}
	
	public static void scCounts() throws IOException {
		
		String scPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/sc_checking.csv";
		File scFile = new File(scPath);
		BufferedWriter scWriter = new BufferedWriter(new FileWriter(scFile));
		scWriter.write("Function Name, Conditions, Ands, Ors, Original Path Count, Transform Path Count\n");
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		int result = 0; 
		
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			String srcName = functionName.substring(4);
			
			if (functionName.contains("test") || functionName.contains("_doscan")) {
				continue;
			}
			
			System.out.println(srcName);
			
			Q function = my_function(srcName);
			Q c = my_cfg(function);
			
			scInfo x = scChecker(c);
			Q transformedGraph = scTransform(srcName);
			if (transformedGraph != null) {
				TopDownDFMultiplicitiesPathCounter transformCounter = new TopDownDFMultiplicitiesPathCounter(true);
				TopDownDFMultiplicitiesPathCounter srcCounter = new TopDownDFMultiplicitiesPathCounter(true);
				com.kcsl.paths.algorithms.PathCounter.CountingResult t = srcCounter.countPaths(c);

				com.kcsl.paths.algorithms.PathCounter.CountingResult r = transformCounter.countPaths(transformedGraph);
				
				if (x != null) {
					result++;
					scWriter.write(srcName + "," + x.getConditions() + "," + x.getAnds() + "," + x.getOrs() + "," + 
					t.getPaths() + "," + r.getPaths()+ "\n");
					scWriter.flush();
				}
			}
			
		}
		scWriter.close();
		System.out.println("Number of Source Functions w/ SC: " + result);
		
	}

}
