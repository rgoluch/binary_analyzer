package com.kcsl.x86;

import org.radare.r2pipe.R2Pipe;
import org.radare.r2pipe.R2Pipe.*;

public class r2Tests {
	public static void main(String[] args) {
		try {
			R2Pipe r2 = new R2Pipe("/Users/RyanGoluch/Desktop/Research/kothari_490/xinu.elf");
			r2.cmd("aaaa");
			String functions = r2.cmd("afl");
			System.out.println(functions);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
