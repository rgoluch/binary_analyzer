package com.kcsl.x86.vectors;

public class VectorResult {
	
	private VectorNode[] bin; 
	private VectorNode[] src;
	
	public VectorResult(VectorNode[] binArr, VectorNode[] srcArr) {
		this.bin = binArr;
		this.src = srcArr;
	}
	
	public VectorNode[] getBinaryArray() {
		return this.bin;
	}
	
	public VectorNode[] getSrcArray() {
		return this.src;
	}
}
