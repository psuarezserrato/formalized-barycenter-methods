#!/usr/bin/env bash
set -euo pipefail

# Create three private GitHub repositories under https://github.com/psuarezserrato
# and push local `main` branches in dependency/submodule order using a GitHub PAT
# (read from GITHUB_PAT, GH_TOKEN, ~/.env, or an interactive hidden prompt).
# The token is passed only in transient HTTP headers and is never written to .git/config.

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
OWNER="psuarezserrato"

if [ -z "${GITHUB_PAT:-}" ] && [ -n "${GH_TOKEN:-}" ]; then
  GITHUB_PAT="$GH_TOKEN"
fi

if [ -z "${GITHUB_PAT:-}" ] && [ -f "$HOME/.env" ]; then
  env_token="$(grep -E '^(GITHUB_PAT|GH_TOKEN)=' "$HOME/.env" | head -n 1 | cut -d= -f2- | sed -e 's/^["'\'']//' -e 's/["'\'']$//' || true)"
  if [ -n "$env_token" ]; then
    GITHUB_PAT="$env_token"
  fi
fi

if [ -z "${GITHUB_PAT:-}" ]; then
  read -r -s -p "Enter GitHub PAT (with 'repo' scope): " GITHUB_PAT
  echo
fi

if [ -z "${GITHUB_PAT:-}" ]; then
  echo "Error: empty GitHub PAT." >&2
  exit 1
fi

echo "==> Verifying GitHub authentication..."
user_resp="$(curl -sS -w "\n%{http_code}" \
  -H "Accept: application/vnd.github+json" \
  -H "Authorization: Bearer $GITHUB_PAT" \
  "https://api.github.com/user")"
user_code="$(printf '%s\n' "$user_resp" | tail -n 1)"
user_body="$(printf '%s\n' "$user_resp" | sed '$d')"

if [ "$user_code" != "200" ]; then
  echo "Error: GitHub authentication failed (HTTP $user_code)." >&2
  printf '%s\n' "$user_body" >&2
  exit 1
fi

auth_login="$(python3 -c 'import json,sys; print(json.load(sys.stdin).get("login",""))' <<< "$user_body")"
echo "    Authenticated as: $auth_login"
if [ -n "$auth_login" ] && [ "$auth_login" != "$OWNER" ]; then
  echo "Warning: authenticated login '$auth_login' differs from expected owner '$OWNER'." >&2
fi

create_private_repo() {
  local name="$1"
  local desc="$2"
  local payload
  payload="$(python3 - "$name" "$desc" <<'PY'
import json, sys
print(json.dumps({"name": sys.argv[1], "private": True, "description": sys.argv[2]}))
PY
)"
  local resp code body
  resp="$(curl -sS -w "\n%{http_code}" \
    -X POST \
    -H "Accept: application/vnd.github+json" \
    -H "Authorization: Bearer $GITHUB_PAT" \
    -d "$payload" \
    "https://api.github.com/user/repos")"
  code="$(printf '%s\n' "$resp" | tail -n 1)"
  body="$(printf '%s\n' "$resp" | sed '$d')"

  if [ "$code" = "201" ]; then
    echo "    Created private repository: $OWNER/$name"
  elif [ "$code" = "422" ]; then
    echo "    Repository $OWNER/$name already exists (HTTP 422); continuing to push."
  else
    echo "Error creating $OWNER/$name (HTTP $code):" >&2
    printf '%s\n' "$body" >&2
    exit 1
  fi
}

echo "==> Creating private GitHub repositories (idempotent)..."
create_private_repo "rcd-entropy-degree-rigidity" \
  "Machine-checked Lean 4 formalization of entropy-degree rigidity for non-collapsed RCD(K, N) and Alexandrov spaces."
create_private_repo "alexandrov-entropy-degree-applications" \
  "Machine-checked Lean 4 formalization of consequences of the Alexandrov entropy-degree theorem (arXiv:2606.30403)."
create_private_repo "formalized-barycenter-methods" \
  "Lean 4 formalization of the Besson-Courtois-Gallot barycenter method, Ruan's octonionic repair, and RCD/Alexandrov extensions."

AUTH_B64="$(printf 'x-access-token:%s' "$GITHUB_PAT" | base64 | tr -d '\n')"

push_repo_main() {
  local dir="$1"
  local label="$2"
  echo "==> Pushing $label (main -> origin/main)..."
  git -C "$dir" -c "http.extraheader=Authorization: Basic $AUTH_B64" push -u origin main
}

push_repo_main "$ROOT_DIR/rcd-entropy-degree-rigidity" "$OWNER/rcd-entropy-degree-rigidity"
push_repo_main "$ROOT_DIR/alexandrov-entropy-degree-applications" "$OWNER/alexandrov-entropy-degree-applications"
push_repo_main "$ROOT_DIR" "$OWNER/formalized-barycenter-methods"

echo
echo "All three private repositories pushed successfully:"
echo "  - https://github.com/$OWNER/formalized-barycenter-methods"
echo "  - https://github.com/$OWNER/rcd-entropy-degree-rigidity"
echo "  - https://github.com/$OWNER/alexandrov-entropy-degree-applications"
