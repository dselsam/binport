PKG = SynthExperiment
include ../../lean4/build/release/stage1/share/lean/lean.mk
all: synthExperiment

SynthExperimentEXE=synthExperiment

synthExperiment: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(SynthExperimentEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libSynthExperiment.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`
