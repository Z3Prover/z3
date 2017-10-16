# Simple wrapper function that runs a command suppressing
# it's output. However it's output will be shown in the
# case that `NO_SUPPRESS_OUTPUT` is set to `1` or the command
# fails.
#
# The use case for this trying to avoid large logs on TravisCI
function run_quiet() {
  if [ "X${NO_SUPPRESS_OUTPUT}" = "X1" ]; then
    "${@}"
  else
    OLD_SETTINGS="$-"
    set +x
    set +e
    TMP_DIR="${TMP_DIR:-/tmp/}"
    STDOUT="${TMP_DIR}/$$.stdout"
    STDERR="${TMP_DIR}/$$.stderr"
    "${@}" > "${STDOUT}" 2> "${STDERR}"
    EXIT_STATUS="$?"
    if [ "${EXIT_STATUS}" -ne 0 ]; then
      echo "Command \"$@\" failed"
      echo "EXIT CODE: ${EXIT_STATUS}"
      echo "STDOUT"
      echo ""
      echo "\`\`\`"
      cat ${STDOUT}
      echo "\`\`\`"
      echo ""
      echo "STDERR"
      echo ""
      echo "\`\`\`"
      cat ${STDERR}
      echo "\`\`\`"
      echo ""
    fi
    # Clean up
    rm "${STDOUT}" "${STDERR}"
    [ "$( echo "${OLD_SETTINGS}" | grep -c 'e')" != "0" ] && set -e
    [ "$( echo "${OLD_SETTINGS}" | grep -c 'x')" != "0" ] && set -x
    return ${EXIT_STATUS}
  fi
}
