
cd ~/clang-cfg-tool/build
rm -rf *
cmake ..
make
./cfg-tool ../test.c
dot -Tpng main_cfg.dot -o cfg.png