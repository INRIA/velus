#!/bin/bash

VELUS="../velus ${VELUSARGS}"

CGREEN='\033[32m'
CRED='\033[31m'
CBLUE='\033[34m'
CDEF='\033[39m'

OK=0
OK_FAILURE=0
OK_SUCCESS=0

for f in ok_*.lus
do
    printf "%b--%s%b\n" "${CGREEN}" "$f" "${CDEF}"
    OK=$(( OK + 1 ))
    if $VELUS "$f" >/dev/null; then
	OK_SUCCESS=$(( OK_SUCCESS + 1 ))
    else
	printf "%bfailed%b\n" "${CRED}" "${CDEF}"
	OK_FAILURE=$(( OK_FAILURE + 1 ))
    fi
done

KO=0
KO_FAILURE=0
KO_SUCCESS=0

for f in ko_*.lus
do
    printf "%b--%s%b\n" "${CBLUE}" "$f" "${CDEF}"
    KO=$(( KO + 1 ))
    if $VELUS "$f" 2>&1; then
	printf "%bfailed%b\n" "${CRED}" "${CDEF}"
	KO_FAILURE=$(( KO_FAILURE + 1 ))
    else
	KO_SUCCESS=$(( KO_SUCCESS + 1 ))
    fi
done

printf "\n"
printf -- "--%bOK success: %d / %d%b\n" \
    "${CGREEN}" "${OK_SUCCESS}" "${OK}" "${CDEF}"
printf -- "--%bKO success: %d / %d%b\n" \
    "${CBLUE}" "${KO_SUCCESS}" "${KO}" "${CDEF}"

if [[ $OK != $OK_SUCCESS || $KO != $KO_SUCCESS ]]
then
    exit 1
fi
