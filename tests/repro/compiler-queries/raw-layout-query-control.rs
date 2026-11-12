#![no_std]
#[derive(Clone, Copy)]
pub enum Residual { A(u8), B(u16) }
#[unsafe(no_mangle)]
pub fn raw_layout_control(x: u8, pair: (u8,bool), array: [u8;3], tag: Residual)
    -> (u8,(u8,bool),[u8;3],Residual) { (x,pair,array,tag) }
