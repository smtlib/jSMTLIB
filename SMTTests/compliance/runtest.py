#! /usr/bin/env python

import sys
import re
import subprocess
import glob

##errorpat = re.compile(r'\(\s*error\s+"[^"]*"\s*\)')
errorpat = re.compile(r'\(\s*error')
lp = re.compile(r'\(')
rp = re.compile(r'\)')

solvers = [
  "z3 -smt2",
  "z3-new -smt2",
  "C:/cygwin/home/dcok/mybin/cvc4-1.4-win32-opt.exe --lang=smt2 --incremental -m",
  "C:/cygwin/home/dcok/mybin/cvc4-1.4-win32-opt.exe --lang=smt2 --incremental -m --strict-parsing",
  "C:/cygwin/home/dcok/apps/yices-2.3.1/yices-2.3.1/bin/yices-smt2.exe --interactive --incremental",
]
solversStdin = [
  "z3 -smt2 -in",
  "z3-new -smt2 -in",
  "C:/cygwin/home/dcok/mybin/cvc4-1.4-win32-opt.exe --lang=smt2 --incremental -m",
  "C:/cygwin/home/dcok/mybin/cvc4-1.4-win32-opt.exe --lang=smt2 --incremental -m --strict-parsing",
  "C:/cygwin/home/dcok/apps/yices-2.3.1/yices-2.3.1/bin/yices-smt2.exe --interactive --incremental",
]

verbose = False

printSuccessIsNotDefault = False
errorOutputOnStderr = False
exitCommandDoesNotEmitSuccess = False
exitOnError = False

def dotest(solver,testfile, configure, usestdin):
    ok = True
    encounteredError = False
    newtestfile = testfile
    if printSuccessIsNotDefault and not configure:
        newtestfile = "tempin"
        tempfile = file(newtestfile,"w")
        tempfile.write("(set-option :print-success true) ; success\n");
        for line in file(testfile, "r"):
            tempfile.write( line )
        tempfile.flush()
        tempfile.close()
    outfile = file("out","w");
    if not configure and errorOutputOnStderr:
        errfile = outfile ## subprocess.STDOUT
        if verbose:
            print "Combining stderr and stdout"
    else:
        errfile = file("err","w")
    if usestdin:
        args = solver.split(" ")
        infile = file(newtestfile,"r")
        retcode = subprocess.call(args,stdin=infile,stdout=outfile,stderr=errfile)
        infile.close()
    else:
        solver = solver + " " + newtestfile
        args = solver.split(" ")
        retcode = subprocess.call(args,stdout=outfile,stderr=errfile)
    outfile.close()
    if not ( not configure and errorOutputOnStderr ) :
        errfile.close()
    infile = file(newtestfile,"r")
    number = 0
    parenlevel = 0
    for line in file("out","r"):
        line = line.rstrip('\r\n')
        number = number + 1
        if verbose:
            print "Actual: " + line
        if parenlevel != 0:
            parenlevel = parenlevel + len(lp.findall(line)) - len(rp.findall(line))
            if verbose:
                print "Parenlevel " + str(parenlevel) + " " + line
            continue
        while True:
            inline = infile.readline()
            if len(inline) == 0:
                break
            inline = inline.strip()
            while len(inline) == 0 or inline[0] == ';':
                if verbose:
                    print "READ: " + inline
                inline = infile.readline()
                if len(inline) == 0:
                    break
                inline = inline.strip()
            if verbose:
                print "READ: " + inline
            info = inline.split(';')
            if len(info) > 1:
                if len(info[1].strip()) == 0:
                    continue
                break
        expected = info[1].strip()
            
        if expected == line or (configure and expected in line):
            pass
            #print "line " + str(number) + " matches"
        elif "|" in expected:
            found = False
            for exp in expected.split("|"):
                if exp == line:
                    found = True
                    break
            if not found:
                ok = False
            if not found and not configure:
                if len(info) > 2:
                    print "FAILURE: " + info[2].strip().replace("$actual",line).replace("$expected",expected)
                else:
                    print "mismatched output in line " + str(number) + ": " + expected + " vs. " + line

        elif errorpat.match(line):
            if expected != "ERROR":
                ok = False
                if not configure:
                    if len(info) > 2:
                        print "FAILURE: " + info[2].strip().replace("$actual",line).replace("$expected",expected)
                    else:
                        print "mismatched output in line " + str(number) + ": " + expected + " vs. " + line
                
            encounteredError = True
            parenlevel = len(lp.findall(line)) - len(rp.findall(line))
            if parenlevel != 0:
                if verbose:
                    print "Parenlevel " + str(parenlevel) + " " + line
                continue
            
            #print "error line " + str(number) + " matches"
        elif not configure:
            if len(info) > 2:
                print "FAILURE: " + info[2].strip().replace("$actual",line).replace("$expected",expected)
            else:
                print "mismatched output in line " + str(number) + ": " + expected + " vs. " + line
            ok = False

    if not (exitOnError and encounteredError):
        inline = infile.readline()
        while len(inline) != 0:
            inline = inline.strip()
            if len(inline) != 0 and inline[0] != ';':
                if not configure and exitCommandDoesNotEmitSuccess and "(exit)" in inline:
                    pass
                else:
                    if verbose:
                        print "Actual output aborted early: " + inline
                    ok = False
                    break
            inline = infile.readline()

    outfile.close()
    infile.close()
    return ok
    

def setModes(usestdin):
        global printSuccessIsNotDefault
        global errorOutputOnStderr
        global exitCommandDoesNotEmitSuccess
        global exitOnError
        exitOnError = False
        print ""
        print "Solver: " + solver + "   use stdin: " + str(usestdin)
        printSuccessIsNotDefault = not dotest(solver, "default-print-success.mode.smt2", True, usestdin)
        exitCommandDoesNotEmitSuccess = not dotest(solver, "exit-emits-success.smt2", True, usestdin)
        exitOnError = dotest(solver, "continued-execution.mode.smt2", True, usestdin)

        ## FIXME - find a way to automatically detect these conditions:
        errorOutputOnStderr = "cvc4" in solver
        
        print "Modes: " + str(printSuccessIsNotDefault) + " " + str(errorOutputOnStderr) + " " + str(exitCommandDoesNotEmitSuccess) + " " + str(exitOnError)
        print ""

if __name__ == "__main__":
    count = 0
    failures = 0
    for solver in solvers:
        setModes(False)
        
        for f in sys.argv[1:]:
            count = count + 1
            if verbose:
                print ">>>>> " + f
            if not dotest(solver, f, False, False):
                ##print "TEST FAILED: " + f + " " + solver
                failures = failures + 1

    for solver in solversStdin:
        setModes(True)
        
        for f in sys.argv[1:]:
            count = count + 1
            if verbose:
                print ">>>>> " + f
            if not dotest(solver, f, False, True):
                ##print "TEST FAILED: " + f + " " + solver
                failures = failures + 1

    print str(failures) + " failures out of " + str(count) + " tests"
    sys.exit(0)    
