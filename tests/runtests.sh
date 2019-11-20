#!/bin/sh

cd $(dirname $0)

VELUS="${VELUS} ${VELUSARGS}"

red=$(tput setaf 1)
blue=$(tput setaf 4)
green=$(tput setaf 2)
normal=$(tput sgr0)

OK=0
OK_FAILURE=0
OK_SUCCESS=0

S=0
for f in *.lus
do
    if [ "${#f}" -gt "$S" ]; then
        S=${#f}
    fi
done

for f in ok_*.lus
do
    printf "%-${S}s" "$f"
    OK=$(( OK + 1 ))
    if $VELUS "$f" >/dev/null 2>/tmp/err; then
	      OK_SUCCESS=$(( OK_SUCCESS + 1 ))
        CHECK="${green}OK${normal}"
    else
	      OK_FAILURE=$(( OK_FAILURE + 1 ))
        ERR=$(</tmp/err)
        CHECK="${red}KO\n  $ERR${normal}"
    fi
    printf " %b\n" "${CHECK}"
done

printf "\n"

KO=0
KO_FAILURE=0
KO_SUCCESS=0

for f in ko_*.lus
do
    printf "%-${S}s" "$f"
    KO=$(( KO + 1 ))
    if $VELUS "$f" >/dev/null 2>/tmp/err; then
	      KO_FAILURE=$(( KO_FAILURE + 1 ))
        CHECK="${red}OK${normal}"
    else
	      KO_SUCCESS=$(( KO_SUCCESS + 1 ))
        ERR=$(</tmp/err)
        CHECK="${blue}KO\n  $ERR${normal}"
    fi
    printf " %b\n" "${CHECK}"
done

printf "\n"
printf -- "OK success: ${green}%d${normal} / %d\n" "${OK_SUCCESS}" "${OK}"
printf -- "KO success: ${blue}%d${normal} / %d\n" "${KO_SUCCESS}" "${KO}"
