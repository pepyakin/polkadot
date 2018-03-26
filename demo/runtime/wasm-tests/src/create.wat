(module
    
    ;; ext_create(code_ptr: u32, code_len: u32, value: u32)
    (import "env" "ext_create" (func $ext_create (param i32 i32 i32)))
    ;; ext_transfer(transfer_to: u32, value: u32)
    (import "env" "ext_transfer" (func $ext_transfer (param i32 i32)))

    (import "env" "memory" (memory 1))

    (func (export "call")
        (call $ext_create
            (i32.const 4)   ;; Pointer to `code`
            (i32.const 144) ;; Length of `code`
            (i32.const 3)   ;; Value to transfer
        )
    )

    ;; Wasm code of `transfer.wasm`. 144 bytes.
    (data (i32.const 4) "\00\61\73\6d\01\00\00\00\01\0f\03\60\03\7f\7f\7f\00\60\02\7f\7f\00\60\00\00\02\33\03\03\65\6e\76\0a\65\78\74\5f\63\72\65\61\74\65\00\00\03\65\6e\76\0c\65\78\74\5f\74\72\61\6e\73\66\65\72\00\01\03\65\6e\76\06\6d\65\6d\6f\72\79\02\00\01\03\02\01\02\07\08\01\04\63\61\6c\6c\00\02\0a\0a\01\08\00\41\04\41\06\10\01\0b\0b\26\01\00\41\04\0b\20\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa")
)
