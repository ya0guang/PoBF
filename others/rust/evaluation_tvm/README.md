# Demo Confidential Task for Apache TVM Machine Learning Framework

You should follow the guide to let it work in the enclave.

1. Install TVM
    ```shell
    $ git clone https://github.com/apache/tvm.git $HOME/tvm
    $ cd $HOME/tvm
    ```

2. **Compile TVM and modify some settings.**
    ```shell
    $ mkdir build && cp ./cmake/config.cmake ./build
    $ cd build
    ```
    Change the following keys to `ON`. This is very important.
    * `USE_MICRO`
    * `USE_MICRO_STANDALONE_RUNTIME`
    
    These keys allow the TVM to build a self-contained ML model; that is, the library build by TVM is a self-runnable bundle with the required interpreter runtime modules such as runtime::GraphExecutor, the graph JSON, and the params, which does not need to link against TVM runtime libraries anymore.

    Then compile it.
    ```shell
    $ cmake .. && make -j$(nproc)
    ```

3. By default, you can set the `TVM_HOME` to `$HOME/tvm` or the parent directory from where the TVM libraries are built.

4. Then you may also need to configure the path python looks for (assume you have set `TVM_HOME`).

```shell
$ export PYTHONPATH=$TVM_HOME/python:$TVM_HOME/topi/python:$TVM_HOME/nnvm/python:${PYTHONPATH}
```

5. Build the standalone library for enclave, which will automatically copies the `libmodel_entry.a` to `./platform_sgx/lib`.

```shell
$ cd ./model_deploy
$ make
```

6. Then rebuild the enclave. Now everything works.