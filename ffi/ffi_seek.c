#include <lean/lean.h>
#include <stdio.h>


int32_t lean_io_fs_SEEK_SET() { return SEEK_SET; }
int32_t lean_io_fs_SEEK_CUR() { return SEEK_CUR; }
int32_t lean_io_fs_SEEK_END() { return SEEK_END; }

extern lean_object* lean_io_fs_handle_seek(lean_object *handle, uint64_t offset, int32_t whence) {
  FILE *fp = (FILE *)(lean_get_external_data(handle));
  int32_t result = fseek(fp, offset, whence);
  return lean_io_result_mk_ok(lean_box(result));
}

/* FILE* fp = lean_to_io_handle(h); */
/* if (fp == NULL) { */
/*     return lean_io_result_mk_error(lean_mk_io_user_error("invalid handle"), w); */
/* } */
/* long long off = lean_unbox_int(offset); */
/* if (fseeko(fp, off, whence) != 0) { */
/*     return lean_io_result_mk_error(lean_mk_io_user_error("seek failed"), w); */
/* } */
/* off_t pos = ftello(fp); */
/* return lean_io_result_mk_ok(lean_box_uint64((uint64_t)pos), w); */
