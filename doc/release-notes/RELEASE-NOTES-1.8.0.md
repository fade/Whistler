# Whistler 1.8.0 Release Notes

## New Features

- **LSM program support.** The loader now supports Linux Security
  Module (LSM) BPF programs. Programs with `lsm/` section names are
  detected automatically, BTF func IDs are resolved from
  `/sys/kernel/btf/vmlinux`, and attachment uses `BPF_LINK_CREATE`.
  `with-bpf-session` handles LSM programs with `(bpf:attach prog)` --
  no target argument needed.

## Bug Fixes

- **Return instruction across branches.** The emitter now always emits
  `mov r0, src` on return, even when the source is already in r0.
  Previously, multi-branch programs where different branches left the
  return value in different registers could produce incorrect code.

- **Parallel move resolution.** Fixed the safety check in the parallel
  move scheduler. The check now correctly tests whether the
  destination register is read as a source by another pending move,
  rather than checking the wrong direction.
