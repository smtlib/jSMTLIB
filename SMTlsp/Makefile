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
LSP4J_VERSION := 1.0.0
LIBS          := $(LSPROOT)/libs
LSP4J_JAR     := $(LIBS)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar
LSP4J_RPC_JAR := $(LIBS)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar
GSON_JAR      := $(LIBS)/gson-2.11.0.jar
LSP4J_CP      := $(LSP4J_JAR):$(LSP4J_RPC_JAR):$(GSON_JAR)

MAVEN := https://repo1.maven.org/maven2

## Build output
CLASSES := $(LSPROOT)/build/classes
JARFILE := $(LSPROOT)/build/smtlib-lsp.jar

## All Java source files (exclude module-info.java — Eclipse artifact)
JAVASRC := $(shell find $(LSPROOT)/src -name '*.java' ! -name 'module-info.java')

.PHONY: all jar compile libs clean .FORCE

all: jar

## Download LSP4J and Gson from Maven Central if not already present
libs: $(LSP4J_JAR) $(LSP4J_RPC_JAR) $(GSON_JAR)

$(LSP4J_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/org/eclipse/lsp4j/org.eclipse.lsp4j/$(LSP4J_VERSION)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar && mv $@.tmp $@ || (rm -f $@.tmp; false)

$(LSP4J_RPC_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/org/eclipse/lsp4j/org.eclipse.lsp4j.jsonrpc/$(LSP4J_VERSION)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar && mv $@.tmp $@ || (rm -f $@.tmp; false)

$(GSON_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/com/google/code/gson/gson/2.11.0/gson-2.11.0.jar && mv $@.tmp $@ || (rm -f $@.tmp; false)

## Compile the LSP server
compile: libs
	@mkdir -p $(CLASSES)
	$(JAVAC) \
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
