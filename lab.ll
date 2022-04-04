; https://stackoverflow.com/questions/41716079/llvm-how-do-i-write-ir-to-file-and-run-it/41833643
; https://stackoverflow.com/questions/7773194/is-it-possible-to-use-llvm-assembly-directly

; https://ecksit.wordpress.com/2011/01/01/hello-world-in-llvm/
; https://kripken.github.io/llvm.js/demo.html

; @str = internal constant [19 x i8] c"Hello LLVM-C world!"

; declare i32 @puts(i8*)

define i32 @main() {
doit:
	; https://blog.yossarian.net/2020/09/19/LLVMs-getelementptr-by-example
	; %0 = call i32 @puts(i8* getelementptr inbounds ([19 x i8], [19 x i8]* @str, i32 0, i32 0))
	%0 = add i32 3, 4
	%1 = add i32 %0, %0
	ret i32 %1
}
