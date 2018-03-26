(module
    ;; ext_set_storage(location_ptr: i32, value_non_null: bool, value_ptr: i32)
    (import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))

    ;; ext_get_storage(location_ptr: i32, value_ptr: i32)
    (import "env" "ext_get_storage" (func $ext_get_storage (param i32 i32)))

    ;; ext_debug(msg_ptr: i32, msg_len: i32)
    ;; (import "env" "ext_debug" (func $ext_debug (param i32 i32)))


    (import "env" "memory" (memory 1))

    (func (export "call")
        (call $ext_get_storage
            (i32.const 4)  ;; Point to a location of the storage.
            (i32.const 36) ;; The result will be written at this address.
        )
        
        
        (i32.store
            (i32.const 36)
            (i32.add
                (i32.load
                    (i32.const 36)
                )
                (i32.const 1)
            )
        )

        (call $ext_set_storage
            (i32.const 4)  ;; Pointer to a location of the storage.
            (i32.const 1)  ;; Value is not null.
            (i32.const 36) ;; Pointer to a data we want to put in the storage.
        )
    )

    ;; Location of storage to put the data. 32 bytes.
    (data (i32.const 4) "\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01")
)
