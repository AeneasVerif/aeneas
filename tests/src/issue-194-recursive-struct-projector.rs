//@ [coq,fstar] subdir=misc
struct AVLNode<T> {
    value: T,
    left: AVLTree<T>,
    right: AVLTree<T>,
}

type AVLTree<T> = Option<Box<AVLNode<T>>>;

fn get_val<T>(x: AVLNode<T>) -> T {
    x.value
}

fn get_left<T>(x: AVLNode<T>) -> AVLTree<T> {
    x.left
}
