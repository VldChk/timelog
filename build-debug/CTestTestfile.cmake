# CMake generated Testfile for 
# Source directory: U:/Projects/timelog
# Build directory: U:/Projects/timelog/build-debug
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
if(CTEST_CONFIGURATION_TYPE MATCHES "^([Dd][Ee][Bb][Uu][Gg])$")
  add_test(timelog_tests "U:/Projects/timelog/build-debug/Debug/test_timelog.exe")
  set_tests_properties(timelog_tests PROPERTIES  _BACKTRACE_TRIPLES "U:/Projects/timelog/CMakeLists.txt;208;add_test;U:/Projects/timelog/CMakeLists.txt;0;")
elseif(CTEST_CONFIGURATION_TYPE MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
  add_test(timelog_tests "U:/Projects/timelog/build-debug/Release/test_timelog.exe")
  set_tests_properties(timelog_tests PROPERTIES  _BACKTRACE_TRIPLES "U:/Projects/timelog/CMakeLists.txt;208;add_test;U:/Projects/timelog/CMakeLists.txt;0;")
elseif(CTEST_CONFIGURATION_TYPE MATCHES "^([Mm][Ii][Nn][Ss][Ii][Zz][Ee][Rr][Ee][Ll])$")
  add_test(timelog_tests "U:/Projects/timelog/build-debug/MinSizeRel/test_timelog.exe")
  set_tests_properties(timelog_tests PROPERTIES  _BACKTRACE_TRIPLES "U:/Projects/timelog/CMakeLists.txt;208;add_test;U:/Projects/timelog/CMakeLists.txt;0;")
elseif(CTEST_CONFIGURATION_TYPE MATCHES "^([Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
  add_test(timelog_tests "U:/Projects/timelog/build-debug/RelWithDebInfo/test_timelog.exe")
  set_tests_properties(timelog_tests PROPERTIES  _BACKTRACE_TRIPLES "U:/Projects/timelog/CMakeLists.txt;208;add_test;U:/Projects/timelog/CMakeLists.txt;0;")
else()
  add_test(timelog_tests NOT_AVAILABLE)
endif()
