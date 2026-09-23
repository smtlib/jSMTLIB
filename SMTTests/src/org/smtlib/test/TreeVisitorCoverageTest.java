package org.smtlib.test;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.IVisitor;
import org.smtlib.SMT;

/** Covers {@link IVisitor.TreeVisitor}, whose methods are otherwise almost entirely
 *  unexercised: nothing in the normal CLI/solver-execution path ever walks a script with a
 *  plain tree-walking visitor (it exists for a future caller -- a linter, a pretty-printer
 *  variant, an analysis pass -- to extend). Parses one script built to exercise as much of
 *  the concrete-syntax variety as will fit in a single, still-parseable script, then walks
 *  every command in it with a fresh {@code TreeVisitor}, confirming it visits the whole tree
 *  without throwing.
 *  <p>
 *  Deliberately parse-only: the script only needs to be syntactically valid, not
 *  semantically consistent (e.g. sorts are mixed and matched freely), since it is never
 *  type-checked or executed against a solver here -- {@link IParser#parseScript()} builds
 *  the AST directly with no type-checking pass in between. */
public class TreeVisitorCoverageTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** parseScript() expects its whole input wrapped in one extra pair of parentheses
     *  around the command sequence (see PrinterCoverageTest#withLines) -- not the plain
     *  concatenated-commands form a normal .smt2 file uses. */
    private static final String SCRIPT =
        "(" +
        "; a leading comment -- becomes its own ICommand.Icomment\n" +
        "(set-info :smt-lib-version 2.7)\n" +
        "(set-option :produce-models true)\n" +
        "(set-info :custom-attr (a b c))\n" + // generic sexpr-valued attribute -> ISexpr.ISeq/IToken
        "(set-logic ALL)\n" +

        "(declare-sort S 0)\n" +
        "(declare-sort-parameter TP)\n" +
        "(declare-const yyy Bool)\n" +
        "(define-const yyy2 Bool false)\n" +
        "(declare-fun le (S S) Bool)\n" +
        "(declare-fun zz () S)\n" +

        "(declare-datatype Color ((red) (green) (blue)))\n" +
        "(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))\n" +

        "(define-sort MyBV () (_ BitVec 8))\n" +
        "(define-sort MyPair (X Y) (Pair X Y))\n" +

        "(declare-const bvvar MyBV)\n" +
        "(declare-const p1 (Pair Int Bool))\n" +
        "(declare-const c Color)\n" +
        "(declare-const rr Real)\n" +
        "(declare-const str String)\n" +

        "(define-fun sq ((x Int)) Int (* x x))\n" +
        "(define-fun-rec fact ((n Int)) Int (ite (= n 0) 1 (* n (fact (- n 1)))))\n" +
        "(define-funs-rec ((isEven ((n Int)) Bool) (isOdd ((n Int)) Bool))\n" +
        "                  ((ite (= n 0) true (isOdd (- n 1)))\n" +
        "                   (ite (= n 0) false (isEven (- n 1)))))\n" +

        "(assert (forall ((x S)(y S)(z S)) (=> (and (le x y)(le y z)) (le x z))))\n" +
        "(assert (exists ((x S)(y S)) (le x y)))\n" +
        "(assert (forall ((x S)(y S)(z S)) (! (=> (and (le x y)(le y z)) (le x z))" +
        "  :pattern ((le x zz)) :pattern ((le y zz) (le zz z)))))\n" +

        "(assert (let ((a 1)(b 2)) (= (+ a b) 3)))\n" +

        "(assert (match c ((red true)(green false)(blue false))))\n" +
        "(assert (match p1 (((pair f s) true))))\n" +

        "(assert (= ((as + Int) 4 3) 7))\n" +
        "(assert (= ((_ extract 3 0) bvvar) #b0000))\n" +
        "(assert (= bvvar #x0F))\n" +
        "(assert (= rr 1.5))\n" +
        "(assert (= str \"hello\"))\n" +

        "(push 1)\n" +
        "(check-sat)\n" +
        "(check-sat-assuming ())\n" +
        "(check-sat-assuming (yyy))\n" +
        "(get-value (yyy rr))\n" +
        "(get-assertions)\n" +
        "(get-model)\n" +
        "(get-proof)\n" +
        "(get-unsat-core)\n" +
        "(get-unsat-assumptions)\n" +
        "(get-option :produce-models)\n" +
        "(get-info :name)\n" +
        "(echo \"hi\")\n" +
        "(pop 1)\n" +
        "(reset-assertions)\n" +
        "(reset)\n" +
        "(exit)\n" +
        ")";

    @Test
    public void walkFullScript() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISource source = config.smtFactory.createSource(SCRIPT, "treeVisitorCoverage");
        IParser parser = config.smtFactory.createParser(config, source);
        ICommand.IScript script = parser.parseScript();
        Assert.assertNotNull("script should parse cleanly with no errors", script);
        Assert.assertFalse("script should contain commands", script.commands().isEmpty());

        IVisitor.TreeVisitor<Object> visitor = new IVisitor.TreeVisitor<Object>();
        script.accept(visitor);
    }
}
