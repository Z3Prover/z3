# Do not add epilogue to Z3_del_context
/Z3_API .*Z3_del_context.*/b endt

# Add error checking epilogue for all Z3_API functions that accept two Z3_contexts
:begincc
# add epilogue for two Z3_context parameters and if a match was found, done with all Z3_contexts and Z3_theorys so jump to endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5\6) quote(dealloc,\"check_error_code(\3);\");/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5) quote(dealloc,\"check_error_code(\3);\");/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5\6) quote(dealloc,\"check_error_code(\3);\")/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5) quote(dealloc,\"check_error_code(\3);\")/g
t endt

# if complete prototype, done with two Z3_contexts
/Z3_API .*(.*);[ 	  ]*$/b endcc
/Z3_API .*(.*)[ 	  ]*$/b endcc

# if incomplete prototype
/Z3_API .*(.*/{

  # read another line
  N

  # add epilogue for two Z3_context parameters and if a match was found, done with all Z3_contexts and Z3_theorys so jump to endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5\6) quote(dealloc,\"check_error_code(\3); check_error_code(\5);\");/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5) quote(dealloc,\"check_error_code(\3); check_error_code(\5);\");/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5\6) quote(dealloc,\"check_error_code(\3); check_error_code(\5);\")/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\(.*\)Z3_context \([a-zA-Z]*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3\4Z3_context \5) quote(dealloc,\"check_error_code(\3); check_error_code(\5);\")/g
  t endt

  # else keep looking for two Z3_contexts
  b begincc
}
:endcc

# Add error checking epilogue for all Z3_API functions that accept one Z3_context
:beginc
# add epilogue for one Z3_context parameter and if a match was found, done with all Z3_contexts and Z3_theorys so jump to endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3\4) quote(dealloc,\"check_error_code(\3);\");/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3) quote(dealloc,\"check_error_code(\3);\");/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\)[ 	  ]*$/Z3_API \1(\2Z3_context \3\4) quote(dealloc,\"check_error_code(\3);\")/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3) quote(dealloc,\"check_error_code(\3);\")/g
t endt

# if complete prototype, done with all Z3_contexts
/Z3_API .*(.*);[ 	  ]*$/b endc
/Z3_API .*(.*)[ 	  ]*$/b endc

# if incomplete prototype
/Z3_API .*(.*/{

  # read another line
  N

  # add epilogue for one Z3_context parameter and if a match was found, done with all Z3_contexts and Z3_theorys so jump to endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3\4) quote(dealloc,\"check_error_code(\3);\");/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\));[ 	  ]*$/Z3_API \1(\2Z3_context \3) quote(dealloc,\"check_error_code(\3);\");/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\)\([^a-zA-Z].*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3\4) quote(dealloc,\"check_error_code(\3);\")/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_context \([a-zA-Z]*\))[ 	  ]*$/Z3_API \1(\2Z3_context \3) quote(dealloc,\"check_error_code(\3);\")/g
  t endt

  # else keep looking for one Z3_context
  b beginc
}
:endc


# Add error checking epilogue for all Z3_API functions that accept a Z3_theory
:begint
# add epilogue for one Z3_theory parameter and if a match was found, done with all Z3_contexts and Z3_theorys so jump to endt
s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\)\([^a-zA-Z].*\));[ 	  ]*$/Z3_API \1(\2Z3_theory \3\4) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\");/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\));[ 	  ]*$/Z3_API \1(\2Z3_theory \3) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\");/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\)\([^a-zA-Z].*\))[ 	  ]*$/Z3_API \1(\2Z3_theory \3\4) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\")/g
t endt
s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\))[ 	  ]*$/Z3_API \1(\2Z3_theory \3) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\")/g
t endt

# if complete prototype, done with all Z3_theorys
/Z3_API .*(.*);[ 	  ]*$/b endt
/Z3_API .*(.*)[ 	  ]*$/b endt

/Z3_API .*(.*/{

  # read another line
  N

  # add epilogue for one Z3_theory parameter and if a match was found, done with all Z3_contexts and Z3_theorys so jump to endt
  s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\)\([^a-zA-Z].*\));[ 	  ]*$/Z3_API \1(\2Z3_theory \3\4) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\");/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\));[ 	  ]*$/Z3_API \1(\2Z3_theory \3) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\");/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\)\([^a-zA-Z].*\))[ 	  ]*$/Z3_API \1(\2Z3_theory \3\4) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\")/g
  t endt
  s/Z3_API \(.*\)(\(.*\)Z3_theory \([a-zA-Z]*\))[ 	  ]*$/Z3_API \1(\2Z3_theory \3) quote(dealloc,\"check_error_code(Z3_theory_get_context(\3));\")/g
  t endt

  # else keep looking for one Z3_theory
  b begint
}
:endt
