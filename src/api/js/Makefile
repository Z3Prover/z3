# Set to 1 to activate API logging
DEBUG=0

all: build/Release/z3.node 

build/Release/z3.node: z3.cc z3consts.js
	node-gyp configure
	node-gyp build

z3.cc: z3.cc.j2 z3.json
	jinja2 -D namespace=z3 -D debug=$(DEBUG) z3.cc.j2 z3.json > z3.cc
