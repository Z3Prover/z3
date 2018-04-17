cmake_minimum_required(VERSION 2.8.8)

project(cmake-ocaml-simple)

set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_CURRENT_SOURCE_DIR}"/cmake)

include(FindOCaml)
include(AddOCaml)
