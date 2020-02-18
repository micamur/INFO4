// Version d'OpenGL
#version 330

in vec4 my_color;
uniform int uni;
in vec4 my_normals;
in vec4 my_position;

out vec4 frag_color;

// Fonction appellee pour chaque fragment
void main()
{
  // Affectation de la couleur du fragment

 if (uni == 1) {
    frag_color = vec4(my_color.rgb+vec3(0.5,0,0),1.0);
 } else if (uni == 2) {
    //frag_color = vec4(my_color.rgb+vec3(0,(uni),0),1.0);
    frag_color = vec4(my_normals);
 } else if (uni == 3) {
    //frag_color = vec4(my_color.rgb+vec3(0,(uni),0),1.0);
    frag_color = vec4(my_position);
 } else if (uni == 4) {
    //frag_color = vec4(my_color.rgb,1.0);
    frag_color = vec4(my_color.rgb+vec3(0.5,0,0),1.0);
    //gl_FragCoord.z
 }
}
