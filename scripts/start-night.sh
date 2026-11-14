#!/usr/bin/env bash
# One command to start a night of Incognita (the owner's routine: CONTRIBUTING.md section 6,
# agents/README.md "Launching a night"). In the loop's clone of main (~/Incognita), as `lean`:
#
#   bash scripts/start-night.sh 02:45 88%     until the next 02:45 in Paris; weekly cap 88 %
#   bash scripts/start-night.sh 6h45 88%      for 6 h 45 min (also 8h, 6h45m, 45m)
#   bash scripts/start-night.sh --stop        stop the running night (report written, token removed)
#
# The night ends at the end time or when the weekly usage of the owner's subscription (the figure of
# claude.ai, Settings, Usage) reaches the cap, whichever comes first. Steps: (1) print what was
# understood and ask for confirmation; (2) create the agents' token with `claude setup-token` (the
# owner follows the link and pastes the code; the token is captured from the output, never shown,
# and written to /etc/incognita/agent.env, root, mode 600); (3) read the weekly usage with it; (4) start
# scripts/night.sh in the tmux session `incognita` with INCOGNITA_PACE=0:100, the deadline and
# INCOGNITA_WEEKLY_CAP, and follow its startup checks.
#
# Options: --yes (no question: confirmation assumed, and no launch without a cap the usage endpoint
# can check), --keep-token (reuse the token already in agent.env), --dry-run (the startup checks and
# one dry pass of the loop, in the foreground: no tmux, no new token).
# The other INCOGNITA_* variables of the environment (e.g. INCOGNITA_PRIVATE_KNOWN) are passed on.
#
# Exit: 0 started (or stopped); 1 refused or failed (nothing runs, and a token created here is
# removed); 2 usage.
set -u -o pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=scripts/lib.sh
. "$here/lib.sh"

SESSION=${INCOGNITA_TMUX_SESSION:-incognita}
CLAUDE_BIN=${INCOGNITA_CLAUDE_BIN:-$(command -v claude || echo "$HOME/.local/bin/claude")}
LOCK=$INCOGNITA_HOME/night.lock

say() { printf '%s\n' "$*"; }
err() { printf '%s\n' "$*" >&2; }
usage() {
  err "Usage : bash scripts/start-night.sh <fin> <plafond> [--yes] [--keep-token] [--dry-run]"
  err "        bash scripts/start-night.sh --stop"
  err "  <fin>      HH:MM (prochaine occurrence, heure de Paris) ou une durée : 8h, 6h45, 6h45m, 45m"
  err "  <plafond>  utilisation hebdomadaire (claude.ai, Settings, Usage) à laquelle aucune tâche ne démarre plus : 88%"
  exit 2
}
night_running() { [ -e "$LOCK" ] && ! flock -n "$LOCK" true; }
session_exists() { command -v tmux >/dev/null && tmux has-session -t "=$SESSION" 2>/dev/null; }
ask() {  # question: 0 if the owner answers yes (y, o, yes, oui)
  local a
  [ -t 0 ] || { err "(pas de terminal pour répondre : refusé ; --yes pour ne rien demander)"; return 1; }
  read -r -p "$1 (y/N) " a || return 1
  case "$a" in y|Y|yes|o|O|oui) return 0 ;; *) return 1 ;; esac
}

yes=0 keep=0 dry=0 stop=0 pos=()
for a in "$@"; do
  case "$a" in
    --yes|-y) yes=1 ;;
    --keep-token) keep=1 ;;
    --dry-run) dry=1 ;;
    --stop) stop=1 ;;
    -h|--help) usage ;;
    -*) err "option inconnue : $a"; usage ;;
    *) pos+=("$a") ;;
  esac
done
mkdir -p "$INCOGNITA_HOME" "$INCOGNITA_LOGS" || { err "impossible de créer $INCOGNITA_HOME"; exit 1; }

# ---------------------------------------------------------------- --stop
if [ "$stop" = 1 ]; then
  if ! night_running; then
    say "Aucune nuit ne tourne."
    session_exists && say "(La session tmux « $SESSION » existe pourtant : tmux attach -t $SESSION, ou tmux kill-session -t $SESSION.)"
    exit 0
  fi
  session_exists || { err "Une nuit tourne (verrou $LOCK) hors de la session tmux « $SESSION » : arrêtez-la par Ctrl-C là où elle tourne."; exit 1; }
  tmux send-keys -t "$SESSION" C-c
  say "Ctrl-C envoyé à la nuit ; attente de la fin (session arrêtée, rapport écrit, jeton retiré)…"
  for _ in $(seq 1 120); do
    night_running || { say "Nuit arrêtée. Rapport : $INCOGNITA_LOGS/<date>-report.md (et l'issue « Night reports »)."; exit 0; }
    sleep 2
  done
  err "La nuit tourne encore après 4 min : tmux attach -t $SESSION pour voir où elle en est."
  exit 1
fi

# ---------------------------------------------------------------- what was asked
[ "${#pos[@]}" = 2 ] || usage
NOW=$(now)
END=$(end_epoch "${pos[0]}" "$NOW") || { err "Fin non comprise : « ${pos[0]} » (HH:MM à Paris, ou une durée comme 8h, 6h45, 45m)."; exit 2; }
CAP=$(parse_cap "${pos[1]}") || { err "Plafond non compris : « ${pos[1]} » (un pourcentage de 1 à 100, comme 88%)."; exit 2; }

# Refusals before anything is asked or created.
if night_running; then
  err "Une nuit tourne déjà (verrou $LOCK) : tmux attach -t $SESSION pour la suivre, bash scripts/start-night.sh --stop pour l'arrêter."
  exit 1
fi
if tauceti_running; then
  err "Le worker Tau Ceti tourne : jamais les deux à la fois. Arrêtez-le d'abord."
  exit 1
fi
if [ "$dry" = 0 ]; then
  command -v tmux >/dev/null || { err "tmux n'est pas installé (sudo apt install tmux)."; exit 1; }
  if session_exists; then
    err "La session tmux « $SESSION » existe déjà (sans nuit en cours) : fermez-la (tmux kill-session -t $SESSION), puis relancez."
    exit 1
  fi
  sudo -n true 2>/dev/null || { err "sudo sans mot de passe est nécessaire (écriture du jeton dans $INCOGNITA_AGENT_ENV)."; exit 1; }
  if [ "$keep" = 0 ] && [ ! -x "$CLAUDE_BIN" ]; then
    err "Claude Code est introuvable ($CLAUDE_BIN) : nécessaire pour claude setup-token."; exit 1
  fi
fi

if [ "$dry" = 1 ]; then tokw="aucun nouveau (essai à blanc)"
elif [ "$keep" = 1 ]; then tokw="celui déjà dans $INCOGNITA_AGENT_ENV"
else tokw="un nouveau, créé par claude setup-token"; fi
say "Fin prévue : $(describe_end "$END" "$NOW") ; plafond hebdomadaire : $CAP %"
say "  (serveur : $(date -u -d "@$END" '+%F %H:%M UTC') ; INCOGNITA_PACE=0:100 ; jeton : $tokw)"
if [ "$dry" = 1 ]; then
  say "Essai à blanc : vérifications de démarrage, puis une passe de la boucle qui ne fait qu'afficher."
elif [ "$yes" = 0 ]; then
  ask "Confirmer ?" || { say "Rien n'a été lancé."; exit 1; }
fi

# From here on, a token written by this script is removed again unless night.sh takes it over.
TOKEN_CREATED=0 LAUNCHED=0
on_exit() { if [ "$TOKEN_CREATED" = 1 ] && [ "$LAUNCHED" = 0 ]; then reset_token >/dev/null 2>&1 && say "Jeton retiré de $INCOGNITA_AGENT_ENV."; fi; }
trap on_exit EXIT
trap 'exit 130' INT TERM HUP

# ---------------------------------------------------------------- the token
if [ "$dry" = 0 ] && [ "$keep" = 0 ]; then
  say ""
  say "Création du jeton des agents (claude setup-token) : ouvrez le lien qui s'affiche, connectez-vous"
  say "avec le compte de l'abonnement, puis collez le code ici. Le jeton est masqué à l'écran et n'est"
  say "écrit que dans $INCOGNITA_AGENT_ENV (root, mode 600)."
  say ""
  exec 4>&1
  rc=0
  tok=$(python3 -I "$here/capture-token.py" --token-fd 3 -- "$CLAUDE_BIN" setup-token 3>&1 1>&4 4>&-) || rc=$?
  exec 4>&-
  say ""
  case "$rc" in
    0) ;;
    1) err "claude setup-token s'est terminé sans afficher de jeton (connexion annulée ?) : rien n'a été lancé."; exit 1 ;;
    2) err "Plusieurs jetons différents dans la sortie de claude setup-token : aucun n'est gardé, rien n'a été lancé."; exit 1 ;;
    *) err "claude setup-token a échoué (code $rc) : rien n'a été lancé."; exit 1 ;;
  esac
  if ! [[ "$tok" =~ ^${TOKEN_RE}$ ]]; then
    tok=""; err "Le jeton capturé n'a pas la forme sk-ant-oat01-… : rien n'a été lancé."; exit 1
  fi
  TOKEN_CREATED=1
  if ! printf '%s\n' "$tok" | write_agent_token; then
    tok=""; err "Impossible d'écrire le jeton dans $INCOGNITA_AGENT_ENV (sudo) : rien n'a été lancé."; exit 1
  fi
  tok=""; unset tok
  token_set || { err "Le jeton n'est pas lisible dans $INCOGNITA_AGENT_ENV : rien n'a été lancé."; exit 1; }
  say "Jeton capturé (masqué) et écrit dans $INCOGNITA_AGENT_ENV."
elif [ "$dry" = 0 ]; then
  token_set || { err "Aucun jeton dans $INCOGNITA_AGENT_ENV (--keep-token) : relancez sans --keep-token."; exit 1; }
fi

# ---------------------------------------------------------------- the weekly usage, with this token
if token_set; then
  if u=$(usage_now 0); then
    read -r w wr s sr src <<< "$u"
    line="Utilisation hebdomadaire actuelle : $w %"
    [[ "$wr" =~ ^[0-9]+$ ]] && line="$line (remise à zéro $(paris_time "$wr"), heure de Paris)"
    [[ "$s" =~ ^[0-9.]+$ ]] && line="$line ; fenêtre de 5 h : $s %"
    say "$line."
    if [ "$src" = lean ]; then
      say "  (Lue par tauceti status avec la connexion Claude de lean : le point d'accès refuse le jeton des agents,"
      say "  dont la portée est user:inference. Si cette connexion expire pendant la nuit, la boucle attend 10 min"
      say "  par essai faute de pouvoir vérifier le plafond ; la renouveler avant : claude auth login.)"
    fi
    case "$(cap_decision "$w" "$CAP")" in
      stop) err "Le plafond est déjà atteint ($w % ≥ $CAP %) : la nuit ne démarre pas."; exit 1 ;;
      short) say "À moins de $INCOGNITA_CAP_MARGIN points du plafond : seules des relectures (et bibliographer, garden) démarreront." ;;
    esac
  elif [[ "$u" == "HTTP 401"* ]]; then
    err "Le jeton est refusé (HTTP 401) : rien n'a été lancé."; exit 1
  elif usage_persistent "$u"; then
    say "Le point d'accès de l'utilisation refuse ce jeton ($u) : le plafond hebdomadaire ne peut pas être vérifié pendant la nuit."
    say "(Solution de repli : la connexion Claude de lean, lue par tauceti status ; la renouveler avec claude auth login, puis relancer.)"
    if [ "$dry" = 1 ]; then :
    elif [ "$yes" = 0 ] && ask "Lancer quand même SANS plafond (seule l'heure de fin compte) ?"; then
      CAP=""
    else
      say "Rien n'a été lancé."; exit 1
    fi
  else
    say "Utilisation illisible pour l'instant ($u) : la boucle la relira avant chaque tâche (et attendra 10 min tant qu'elle reste illisible)."
  fi
fi

# ---------------------------------------------------------------- night.sh
NIGHT=$(date +%F)
envs=(INCOGNITA_PACE=0:100 "INCOGNITA_DEADLINE=$(date -d "@$END" +%H:%M)" "INCOGNITA_DEADLINE_EPOCH=$END"
      "INCOGNITA_WEEKLY_CAP=$CAP" "INCOGNITA_NIGHT=$NIGHT")
while IFS= read -r v; do
  case "$v" in
    INCOGNITA_PACE|INCOGNITA_DEADLINE|INCOGNITA_DEADLINE_EPOCH|INCOGNITA_WEEKLY_CAP|INCOGNITA_NIGHT|INCOGNITA_DRY_RUN) ;;
    *) envs+=("$v=${!v}") ;;
  esac
done < <(compgen -e | grep '^INCOGNITA_')
if [ "$dry" = 1 ]; then
  cd "$INCOGNITA_REPO" || exit 1
  env "${envs[@]}" INCOGNITA_DRY_RUN=1 bash "$here/night.sh"
  exit $?
fi

logf=$INCOGNITA_LOGS/$NIGHT.log
off=0; [ -f "$logf" ] && off=$(wc -c < "$logf")
# Several arguments: tmux runs them as they are, without a shell (no quoting to get wrong).
if ! tmux new-session -d -s "$SESSION" -c "$INCOGNITA_REPO" env "${envs[@]}" bash "$here/night.sh"; then
  err "tmux n'a pas pu créer la session « $SESSION » : rien n'a été lancé."; exit 1
fi
LAUNCHED=1   # night.sh owns the token now: it removes it at the end, whatever the way out
say ""
say "Nuit lancée dans tmux (session « $SESSION »). Vérifications de démarrage (jusqu'à 3 min)…"
started=""
for _ in $(seq 1 60); do
  sleep 3
  new=$(tail -c +"$(( off + 1 ))" "$logf" 2>/dev/null)
  if [[ "$new" == *"== loop start"* ]]; then started=yes; break; fi
  if ! session_exists; then started=no; break; fi
done
case "$started" in
  yes) say "Démarrage réussi : la boucle tourne." ;;
  no) err "La nuit s'est arrêtée au démarrage :"
      printf '%s\n' "$new" | grep -E 'FAILED|fatal|another scripts/night.sh|cannot' | sed 's/^/  /' >&2
      err "Journal : $logf ; rapport : $INCOGNITA_LOGS/$NIGHT-report.md (le jeton a été retiré)."
      exit 1 ;;
  *) say "Les vérifications continuent (connexion Claude dans le bac à sable, synchronisation) : suivez-les ci-dessous." ;;
esac
say ""
say "  Suivre :     tmux attach -t $SESSION      (se détacher : Ctrl-b puis d)"
say "  Journal :    tail -f $logf"
say "  Arrêter :    bash scripts/start-night.sh --stop   (ou Ctrl-C dans la session tmux) :"
say "               la tâche en cours est arrêtée, le rapport écrit, le jeton retiré."
exit 0
