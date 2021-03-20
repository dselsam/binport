PKG = MetaCheck
include ../../lean4/build/release/stage1/share/lean/lean.mk
all: metaCheck

MetaCheckEXE=metaCheck

metaCheck: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(MetaCheckEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libMetaCheck.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`
