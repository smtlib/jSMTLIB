/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import org.smtlib.SMT.Configuration;

// Items not implemented:
//   attributed expressions
//   get-values get-assignment get-proof get-unsat-core
//   some error detection and handling

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into Z3 commands */
public class Solver_z3_4_4 extends Solver_z3_4_3 {
    
    protected String NAME_VALUE = "z3-4.4";
    protected String AUTHORS_VALUE = "Leonardo de Moura and Nikolaj Bjorner";
    protected String VERSION_VALUE = "4.4";
    
    public Solver_z3_4_4(Configuration smtConfig, String executable) {
        super(smtConfig, executable);
    }

}
