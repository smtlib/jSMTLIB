mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir  := $(dir $(mkfile_path))
LSPROOT     := $(patsubst %/,%,$(mkfile_dir))

## jSMTLIB jar — built by the sibling SMT project
SMTROOT    := $(LSPROOT)/../SMT
SMTLIB_JAR := $(SMTROOT)/jSMTLIB.jar

## Use the system javac/jar (no custom JDK needed for jSMTLIB)
JAVAC := javac
JAR   := jar

## LSP4J jars (downloaded into libs/ on first build)
LIBS          := $(LSPROOT)/libs
LSP4J_JAR     := $(LIBS)/org.eclipse.lsp4j-1.0.0.jar
LSP4J_RPC_JAR := $(LIBS)/org.eclipse.lsp4j.jsonrpc-1.0.0.jar
GSON_JAR      := $(LIBS)/gson-2.11.0.jar
LSP4J_CP      := $(LSP4J_JAR):$(LSP4J_RPC_JAR):$(GSON_JAR)


## Build output
CLASSES := $(LSPROOT)/build/classes
JARFILE := $(LSPROOT)/build/smtlib-lsp.jar

## All Java source files (exclude module-info.java — Eclipse artifact)
JAVASRC := $(shell find $(LSPROOT)/src -name '*.java' ! -name 'module-info.java')

.PHONY: all jar compile libs clean .FORCE

all: jar

## Fetch LSP4J and Gson from Maven Central into libs/ if absent, checking each SHA-256 (libs.sha256)
libs:
	bash $(LSPROOT)/fetch-jars $(LIBS) $(LSPROOT)/libs.sha256

## Compile the LSP server
compile: libs
	@mkdir -p $(CLASSES)
	$(JAVAC) -Xlint:all \
	    -cp $(SMTLIB_JAR):$(LSP4J_CP) \
	    -d $(CLASSES) \
	    $(JAVASRC)

## Package into an executable jar with embedded classpath manifest
jar: compile
	$(JAR) --create --file=$(JARFILE) \
	       --main-class=org.smtlib.lsp.ServerLauncher \
	       -C $(CLASSES) .

clean: .FORCE
	rm -rf $(LSPROOT)/build

.FORCE:
