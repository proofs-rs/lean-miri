#define _GNU_SOURCE 1
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>
typedef struct { uint32_t status,kind,raw_present; int32_t raw; uint64_t count; } stdio_result;
_Static_assert(sizeof(stdio_result)==24, "stdio result ABI size");
_Static_assert(offsetof(stdio_result,count)==16, "stdio result ABI count offset");
extern stdio_result lean_miri_stdio_rust_write(uint32_t,const uint8_t*,size_t);
extern stdio_result lean_miri_stdio_rust_flush(void);
extern stdio_result lean_miri_stdio_rust_adopt(uint32_t);
extern stdio_result lean_miri_stdio_rust_control(const uint8_t*,size_t);
extern stdio_result lean_miri_stdio_rust_close(void);
int lean_miri_stdio_check_fd(int fd) {
 struct stat st;
 if (fd<3) {errno=EINVAL;return -1;}
 if(fstat(fd,&st)<0)return -1;
 if(!S_ISREG(st.st_mode)){errno=EINVAL;return -1;}
 int flags=fcntl(fd,F_GETFD);
 if(flags<0)return -1;
 return fcntl(fd,F_SETFD,flags|FD_CLOEXEC);
}
static lean_obj_res encode(stdio_result r) {
 lean_object *b=lean_alloc_sarray(1,24,24);
 uint8_t *p=lean_sarray_cptr(b);
 uint32_t fields[4]={r.status,r.kind,r.raw_present,(uint32_t)r.raw};
 for(size_t j=0;j<4;j++)for(size_t i=0;i<4;i++)p[4*j+i]=(uint8_t)(fields[j]>>(8*i));
 for(size_t i=0;i<8;i++)p[16+i]=(uint8_t)(r.count>>(8*i));
 return lean_io_result_mk_ok(b);
}
LEAN_EXPORT lean_obj_res lean_miri_stdio_write(uint32_t s,b_lean_obj_arg b,lean_obj_arg world){
 (void)world;return encode(lean_miri_stdio_rust_write(s,lean_sarray_cptr(b),lean_sarray_size(b)));
}
LEAN_EXPORT lean_obj_res lean_miri_stdio_flush(lean_obj_arg world){(void)world;return encode(lean_miri_stdio_rust_flush());}
LEAN_EXPORT lean_obj_res lean_miri_stdio_adopt(uint32_t fd,lean_obj_arg world){(void)world;return encode(lean_miri_stdio_rust_adopt(fd));}
LEAN_EXPORT lean_obj_res lean_miri_stdio_control(b_lean_obj_arg b,lean_obj_arg world){(void)world;return encode(lean_miri_stdio_rust_control(lean_sarray_cptr(b),lean_sarray_size(b)));}
LEAN_EXPORT lean_obj_res lean_miri_stdio_close(lean_obj_arg world){(void)world;return encode(lean_miri_stdio_rust_close());}
