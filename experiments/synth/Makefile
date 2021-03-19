PKG = SynthExperiment
include ../../lean4/build/release/stage1/share/lean/lean.mk
all: synthExperiment

SynthExperimentEXE=synthExperiment
Lean4Exe=
LIB4=./Lib4
LEAN3_PATH=./lean3/library:./lean3/leanpkg:./mathlib/src
LEAN4_PATH=./lean4/build/release/stage1/lib/lean:$(LIB4)

synthExperiment: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(SynthExperimentEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libSynthExperiment.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`
