package com.kcsl.x86.vectors;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.xcsg.XCSG;


public class VectorNode {

	private String name; 
	private long incoming; 
	private long outgoing; 
	private String color;
	
	public VectorNode(String name, long in, long out) {
		this.name = name;
		this.incoming = in;
		this.outgoing = out;
	}
	
	public long getIncoming() {
		return this.incoming;
	}
	
	public long getOutgoing() {
		return this.outgoing;
	}
	
	public void setIncoming(Node n) {
		this.incoming = n.in().taggedWithAll(XCSG.ControlFlow_Edge).size();
	}
	
	public void setOutgoing(Node n) {
		this.outgoing = n.out().taggedWithAll(XCSG.ControlFlow_Edge).size();
	}
	
	public String nodeToString() {
		return "("+this.incoming+":"+this.outgoing+")";
	}
	
}
