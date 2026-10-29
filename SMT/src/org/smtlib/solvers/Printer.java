package org.smtlib.solvers;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

import org.smtlib.INode;
import org.smtlib.IExpr;
import org.smtlib.IPos;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IForall;
import org.smtlib.Utils;


public class Printer extends org.smtlib.sexpr.Printer {

    /** Creates a printer object that follows the given Configuration's rules. */
    public Printer(org.smtlib.SMT.Configuration smtConfig, Writer w) {
        super(smtConfig, w);
    }

    @Override
    public Printer newPrinter(Writer w) {
        return new Printer(smtConfig, w);
    }

    @Override
    public <T extends INode> String toString(T expr) {
        try {
            StringWriter sw = new StringWriter();
            expr.accept(new Printer(smtConfig, sw));
            return sw.toString();
        } catch (IVisitor.VisitorException e) {
            return "<<ERROR: " + e.getMessage() + ">>";
        }
    }

    /** Writes the given expression and outputs as a String, following the given
     *  Configuration's rules. */
    static public <T extends INode> String write(org.smtlib.SMT.Configuration smtConfig, T e) {
        try {
            StringWriter w = new StringWriter();
            e.accept(new Printer(smtConfig, w));
            return w.toString();
        } catch (IVisitor.VisitorException ex) {
            return "<<ERROR: " + ex.getMessage() + ">>";
        }
    }

    /** Writes the given expression to the given writer, following the given
     *  Configuration's rules. */
    static public <T extends INode> void write(org.smtlib.SMT.Configuration smtConfig, Writer w, T e) throws IVisitor.VisitorException {
        e.accept(new Printer(smtConfig, w));
        try { w.flush(); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
    }

    /** Writes the given expression to the given stream, following the given
     *  Configuration's rules. */
    static public <T extends INode> void write(org.smtlib.SMT.Configuration smtConfig, PrintStream w, T e)  throws IVisitor.VisitorException {
        Writer wr = new OutputStreamWriter(w);
        e.accept(new Printer(smtConfig, wr));
        try {
            wr.flush(); w.flush();
        } catch (IOException ex) {
            throw new IVisitor.VisitorException(ex);
        }
    }

    @Override
    public Void visit(IForall e) throws IVisitor.VisitorException {
        if (!hasBoolParameter(e.parameters())) return super.visit(e);
        printQuantifierUnfoldingBoolParams(Utils.FORALL, e.parameters(), e.expr(), e.pos());
        return null;
    }

    @Override
    public Void visit(IExists e) throws IVisitor.VisitorException {
        if (!hasBoolParameter(e.parameters())) return super.visit(e);
        printQuantifierUnfoldingBoolParams(Utils.EXISTS, e.parameters(), e.expr(), e.pos());
        return null;
    }

    private static boolean hasBoolParameter(List<IDeclaration> params) {
        for (IDeclaration a: params) if (a.sort().isBool()) return true;
        return false;
    }

    /** Prints a forall/exists over one or more Bool-sorted parameters as a case split: each such
     *  parameter becomes a pair of (let ((b true/false)) ...) cases, conjoined for forall and
     *  disjoined for exists, around a quantifier over the remaining parameters (or just the body).
     *  yices2, run incrementally, rejects every quantifier; this lets it answer those over Bool
     *  variables only, bringing it closer to SMT-LIB behavior. */
    private void printQuantifierUnfoldingBoolParams(String keyword, List<IDeclaration> params, IExpr body, IPos pos) throws IVisitor.VisitorException {
        int idx = -1;
        for (int i = 0; i < params.size(); i++) {
            if (params.get(i).sort().isBool()) { idx = i; break; }
        }
        if (idx < 0) {
            try {
                if (params.isEmpty()) {
                    body.accept(this);
                } else {
                    w.append("(" + keyword + " (");
                    for (IDeclaration a: params) { a.accept(this); w.append(" "); }
                    w.append(") ");
                    body.accept(this);
                    w.append(")");
                }
            } catch (IOException ex) {
                throw new IVisitor.VisitorException(ex,pos);
            }
            return;
        }
        IDeclaration boolParam = params.get(idx);
        List<IDeclaration> rest = new ArrayList<IDeclaration>(params);
        rest.remove(idx);
        String combiner = Utils.FORALL.equals(keyword) ? "and" : "or";
        try {
            w.append("(" + combiner + " (" + Utils.LET + " ((");
            boolParam.parameter().accept(this);
            w.append(" true)) ");
        } catch (IOException ex) {
            throw new IVisitor.VisitorException(ex,pos);
        }
        printQuantifierUnfoldingBoolParams(keyword, rest, body, pos);
        try {
            w.append(") (" + Utils.LET + " ((");
            boolParam.parameter().accept(this);
            w.append(" false)) ");
        } catch (IOException ex) {
            throw new IVisitor.VisitorException(ex,pos);
        }
        printQuantifierUnfoldingBoolParams(keyword, rest, body, pos);
        try {
            w.append("))");
        } catch (IOException ex) {
            throw new IVisitor.VisitorException(ex,pos);
        }
    }
}
