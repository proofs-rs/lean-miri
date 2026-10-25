fn corpus()->Vec<u128>{
 let mut result=vec![0,u128::MAX,1,1u128<<127,0x00112233445566778899aabbccddeeff];
 let mut seed=0x0123456789abcdefu128;
 for _ in 0..16{seed=seed.wrapping_mul(47026247687942121848144207491837523525).wrapping_add(117397592171526113268558934119004209487);result.push(seed)}
 result
}
fn main(){for block in corpus(){
 for inverse in [false,true]{
  let mut a=aes::Block::from(block.to_le_bytes());let mut b=a;
  aes::qa_mix32(&mut a,inverse);aes::qa_mix64(&mut b,inverse);assert_eq!(a,b);
  println!("{}",u128::from_le_bytes(a.as_slice().try_into().unwrap()));
 }
 for key in corpus(){for inverse in [false,true]{
  let key=aes::Block::from(key.to_le_bytes());let mut a=aes::Block::from(block.to_le_bytes());let mut b=a;
  aes::qa_round32(&mut a,&key,inverse);aes::qa_round64(&mut b,&key,inverse);assert_eq!(a,b);
  println!("{}",u128::from_le_bytes(a.as_slice().try_into().unwrap()));
 }}
}}
