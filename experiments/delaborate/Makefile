PKG = Delaborate
include $(LEAN4_S1_MK)
all: Delaborate

DelaborateEXE=delaborate

Delaborate: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(DelaborateEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libDelaborate.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc`
