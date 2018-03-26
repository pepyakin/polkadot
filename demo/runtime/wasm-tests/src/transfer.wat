(module
    
    ;; ext_create(code_ptr: u32, code_len: u32, value: u32)
    (import "env" "ext_create" (func $ext_create (param i32 i32 i32)))
    ;; ext_transfer(transfer_to: u32, value: u32)
    (import "env" "ext_transfer" (func $ext_transfer (param i32 i32)))

    (import "env" "memory" (memory 1))

    (func (export "call")
        (call $ext_transfer
            (i32.const 4) ;; Pointer to "Transfer to" address
            (i32.const 6)
        )
    )

    ;; Location of storage to put the data. 32 bytes.
    (data (i32.const 4) "\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa")
)
