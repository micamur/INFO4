// Version d'OpenGL
#version 330

// Donnees d'entree
in vec3 in_position;

out vec2 coords;

// Fonction appellee pour chaque sommet
void main() {
  gl_Position = vec4(in_position, 1.0);
  
  coords = in_position.xy*0.5+0.5; // remap [-1,1] to [0,1]
}
