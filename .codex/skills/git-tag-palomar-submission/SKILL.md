---
name: git-tag-palomar-submission
description: Create and push an annotated version tag for the current commit after it has already been submitted to Palomar. Use only for this post-submission tagging workflow.
---

# Git tag Palomar submission

Create and push an annotated tag for the current `HEAD` after its Palomar
submission. This skill does not submit to Palomar and does not create a GitHub
Release.

## Mandatory confirmation gate

Before inspecting releases, reading remotes, or running any command, ask this
blocking question:

> Please confirm that the current `HEAD` commit, not merely another commit or
> uncommitted work—has already been submitted to Palomar. Reply `yes` to tag
> and push this exact commit.

Proceed only after an unambiguous affirmative response. If the response is
negative, ambiguous, or absent, stop without running any command.

## Choose the tag

After confirmation, identify the GitHub repository named by the `origin`
remote without using a Git command (read `.git/config` directly). Use a
read-only GitHub release lookup for that exact repository, paginating until
every release has been considered; do not rely on a first page or its creation
order.

Consider only published, non-draft, non-prerelease releases whose tags exactly
match `vX.Y.Z`, with nonnegative decimal `X`, `Y`, and `Z`. Compare versions
numerically, not lexically.

* If no such release is at least `v1.0.0`, choose `v1.0.0`.
* Otherwise select the greatest such release and increment only `Z` by one.
  Thus an existing `v1.0.0` release yields `v1.0.1`, and `v2.4.9` yields
  `v2.4.10`.
* Check that the proposed tag does not already exist on GitHub. If an
  unreleased tag occupies it, keep incrementing `Z` until the first unused
  tag. If the release or tag lookup cannot be performed reliably, stop before
  making any change.

## Execute exactly three Git commands

On the successful path, run exactly these Git commands, in this order, with
the chosen concrete tag substituted for `<tag>`:

```text
git tag -a <tag> -m "Palomar submission snapshot"
git push origin <tag>
git rev-parse HEAD
```

Do not run any other Git command. Do not force a tag or push, create a commit,
change branches, amend history, push other refs, or create a GitHub Release.
Run each command separately and stop immediately if one fails; do not attempt
later commands after a failure.

After success, report the chosen tag and the SHA printed by the third command.
