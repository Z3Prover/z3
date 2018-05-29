DEBUG=0

all: cdecl2json.byte z3.cc
	node-gyp configure
	node-gyp build

cdecl2json.byte: cdecl2json.ml
	corebuild -package yojson -package cil cdecl2json.byte
	
z3_combined.h: ../../api/z3.h
	gcc -E ../../api/z3.h > z3_combined.h

z3.json: z3_combined.h cdecl2json.byte
	./cdecl2json.byte -prefix Z3 -o z3.json z3_combined.h

z3_consts.js: z3.consts.j2 z3.json
	jinja2 z3.consts.j2 z3.json > z3_consts.js

z3.cc: z3.cc.j2 z3.json
	jinja2 -D namespace=z3 -D debug=$(DEBUG) z3.cc.j2 z3.json > z3.cc
